import { copyFile, mkdir, mkdtemp, open, readFile, readdir, rename, rm } from "node:fs/promises";
import { spawn } from "node:child_process";
import { dirname, extname, join, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const scriptDirectory = dirname(fileURLToPath(import.meta.url));
const projectRoot = resolve(scriptDirectory, "..");
const outputDirectory = join(projectRoot, "js");
const lockPath = join(projectRoot, ".deductrium-build.lock");

const delay = milliseconds => new Promise(resolveDelay => setTimeout(resolveDelay, milliseconds));

async function readLockOwner() {
    try {
        return JSON.parse(await readFile(lockPath, "utf8"));
    } catch {
        return null;
    }
}

function processIsAlive(pid) {
    if (!Number.isInteger(pid) || pid <= 0) return false;
    try {
        process.kill(pid, 0);
        return true;
    } catch (error) {
        // EPERM means the process exists but is not signalable on Windows.
        return error?.code === "EPERM";
    }
}

async function acquireBuildLock({ timeoutMs = 10 * 60 * 1000 } = {}) {
    const startedAt = Date.now();
    while (true) {
        try {
            const handle = await open(lockPath, "wx");
            await handle.writeFile(JSON.stringify({ pid: process.pid, startedAt }));
            return async () => {
                await handle.close().catch(() => undefined);
                await rm(lockPath, { force: true }).catch(() => undefined);
            };
        } catch (error) {
            if (error?.code !== "EEXIST") throw error;
            const owner = await readLockOwner();
            const lockAge = Date.now() - Number(owner?.startedAt ?? 0);
            if (owner && !processIsAlive(owner.pid) && lockAge > 5_000) {
                await rm(lockPath, { force: true }).catch(() => undefined);
                continue;
            }
            if (Date.now() - startedAt >= timeoutMs) {
                throw new Error("等待其他 Deductrium 构建完成超时");
            }
            await delay(100);
        }
    }
}

async function collectFiles(directory) {
    const entries = await readdir(directory, { withFileTypes: true });
    const files = [];
    for (const entry of entries) {
        const path = join(directory, entry.name);
        if (entry.isDirectory()) files.push(...await collectFiles(path));
        else if (entry.isFile()) files.push(path);
    }
    return files;
}

async function runTypeScript(stagingDirectory) {
    const tscPath = resolve(projectRoot, "node_modules/typescript/bin/tsc");
    const args = [
        tscPath,
        "-p", resolve(projectRoot, "tsconfig.json"),
        "--outDir", stagingDirectory,
        "--pretty", "false"
    ];
    await new Promise((resolveRun, rejectRun) => {
        const child = spawn(process.execPath, args, {
            cwd: projectRoot,
            stdio: "inherit",
            windowsHide: true
        });
        child.once("error", rejectRun);
        child.once("close", code => {
            if (code === 0) resolveRun();
            else rejectRun(new Error(`TypeScript 编译失败（退出码 ${code ?? "unknown"}）`));
        });
    });
}

async function expectedOutputPaths() {
    const sourceFiles = await collectFiles(join(projectRoot, "src"));
    return sourceFiles
        .filter(path => extname(path) === ".ts")
        .flatMap(path => {
            const output = relative(join(projectRoot, "src"), path).replace(/\.ts$/u, ".js");
            return [output, `${output}.map`];
        });
}

async function assertCompleteStaging(stagingDirectory) {
    const expected = await expectedOutputPaths();
    const missing = [];
    for (const output of expected) {
        try {
            await readFile(join(stagingDirectory, output));
        } catch {
            missing.push(output);
        }
    }
    if (missing.length) {
        throw new Error(`TypeScript 输出不完整，缺少：${missing.join(", ")}`);
    }
}

async function publishStaging(stagingDirectory) {
    await mkdir(outputDirectory, { recursive: true });
    const files = (await collectFiles(stagingDirectory)).sort();
    let sequence = 0;
    for (const source of files) {
        const destination = join(outputDirectory, relative(stagingDirectory, source));
        await mkdir(dirname(destination), { recursive: true });
        const temporaryDestination = `${destination}.tmp-${process.pid}-${sequence++}`;
        await copyFile(source, temporaryDestination);
        // A rename of a file is atomic on the supported platforms. Existing
        // output stays readable until the complete replacement is available.
        await rename(temporaryDestination, destination);
    }
}

export async function buildProject() {
    const releaseLock = await acquireBuildLock();
    let stagingDirectory = null;
    try {
        stagingDirectory = await mkdtemp(join(projectRoot, ".deductrium-build-"));
        await runTypeScript(stagingDirectory);
        await assertCompleteStaging(stagingDirectory);
        await publishStaging(stagingDirectory);
    } finally {
        if (stagingDirectory) await rm(stagingDirectory, { recursive: true, force: true });
        await releaseLock();
    }
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
    try {
        await buildProject();
    } catch (error) {
        console.error(error instanceof Error ? error.message : String(error));
        process.exitCode = 1;
    }
}
