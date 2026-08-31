import assert from "node:assert/strict";
import { access, readdir, rm, writeFile } from "node:fs/promises";
import { spawn } from "node:child_process";
import { dirname, join, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const outputDirectory = join(projectRoot, "js");

function runBuild() {
    return new Promise((resolveBuild, rejectBuild) => {
        const child = spawn(process.execPath, ["scripts/build.mjs"], {
            cwd: projectRoot,
            stdio: ["ignore", "pipe", "pipe"],
            windowsHide: true
        });
        let output = "";
        child.stdout.on("data", chunk => { output += chunk; });
        child.stderr.on("data", chunk => { output += chunk; });
        child.once("error", rejectBuild);
        child.once("close", code => {
            if (code === 0) resolveBuild(output);
            else rejectBuild(new Error(`并发构建失败（${code}）：${output}`));
        });
    });
}

const sentinel = join(outputDirectory, ".issue-14-sentinel.js");
await writeFile(sentinel, "export const sentinel = true;\n");
try {
    await Promise.all([runBuild(), runBuild()]);

    // The old prebuild deleted the entire output directory. A successful
    // concurrent build must retain an existing reader-visible file instead.
    await access(sentinel);

    const sourceFiles = [];
    async function collect(directory) {
        for (const entry of await readdir(directory, { withFileTypes: true })) {
            const path = join(directory, entry.name);
            if (entry.isDirectory()) await collect(path);
            else if (entry.isFile() && path.endsWith(".ts")) sourceFiles.push(path);
        }
    }
    await collect(join(projectRoot, "src"));
    for (const source of sourceFiles) {
        const output = join(outputDirectory, relative(join(projectRoot, "src"), source).replace(/\.ts$/u, ".js"));
        await access(output);
        await access(`${output}.map`);
    }
} finally {
    await rm(sentinel, { force: true });
}

console.log("issue #14 concurrent build output regression passed");
