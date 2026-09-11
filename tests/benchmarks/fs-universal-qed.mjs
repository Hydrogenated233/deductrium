import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { gunzipSync } from "node:zlib";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { Worker } from "node:worker_threads";
import { initFormalSystem } from "../../js/fs/initial.js";
import { SavesParser } from "../../js/fs/savesparser.js";
import { InferenceProofAssistant } from "../../js/fs/proof-assistant.js";

const mode = process.argv[2] ?? "quantified";
if (!["quantified", "split", "original", "worker"].includes(mode)) throw new Error("Unknown mode");
if (!process.argv.includes("--child")) {
    const result = spawnSync(process.execPath, [fileURLToPath(import.meta.url), mode, "--child"], {
        timeout: 240_000, encoding: "utf8", maxBuffer: 1024 * 1024
    });
    process.stdout.write(result.stdout ?? "");
    process.stderr.write(result.stderr ?? "");
    if (result.error) console.error(result.error);
    process.exit(result.status ?? 1);
}

const fixture = JSON.parse(gunzipSync(readFileSync(
    new URL("../fixtures/fs-issue-46-union.json.gz", import.meta.url)
)));
const data = fixture.save;
data[7].activeId = data[7].pages.find(page => page.name === "elV1").id;
data[6] = [];
const fs = new SavesParser(false).deserializeArr(initFormalSystem(false).fs, data).fs;
const boundary = data[5].indexOf("xFamilyUnionCompatibleCore");
assert.ok(boundary > 0);
const rules = new Set(data[5].slice(0, boundary));
const quantified = [
    "intros A c g hg hc",
    "have hd := xFamilyUnionData",
    "specialize hd A c g hg",
    "have hchain := xFamilyInitialChain",
    "specialize hchain A c g hg hc",
    "have hall := xFamilyAllCompatible",
    "specialize hall A c g hg",
    "have hcomp := xChainUnionCompatible",
    "specialize hcomp A c g hd hchain hall",
    "exact hcomp"
];

async function run(name, target, commands) {
    const assistant = new InferenceProofAssistant(fs, target, {
        allowMcpt: false, ruleNames: rules, pageId: data[7].activeId
    });
    const start = performance.now();
    for (const command of commands) assistant.apply(command);
    const applyMs = performance.now() - start;
    assert.equal(assistant.snapshot().complete, true);
    const qedStart = performance.now();
    if (mode === "worker") {
        const preview = assistant.materializeQed(name);
        const recipe = preview.steps[0].assistant;
        const save = new SavesParser(false).serialize({
            formalSystem: fs, deductions: data[5], metarules: [],
            getProps: () => fs.propositions, pageStore: fs.inferencePages
        });
        const worker = new Worker(new URL("./fs-qed-worker.mjs", import.meta.url));
        try {
            const result = await new Promise((resolve, reject) => {
                worker.once("message", value => value.error ? reject(new Error(value.error)) : resolve(value));
                worker.once("error", reject);
                worker.once("exit", code => reject(new Error(`Worker exited without a result: ${code}`)));
                worker.postMessage({
                    save, creative: false, fastMetaRules: recipe.fastMetaRules ?? "cvuqe><:#zZQR",
                    metarules: [],
                    target: {
                        kind: "qed", theorem: recipe.theorem, history: commands,
                        pageId: data[7].activeId, name, ruleNames: [...rules],
                        allowMcpt: false, allowIfft: true, allowIfftEu: true
                    }
                });
            });
            assert.equal(result.qed?.committed, true);
            assert.ok(result.deductions[name]);
            assert.equal(fs.deductions[name], undefined, "worker leaves its caller's source untouched");
        } finally {
            await worker.terminate();
        }
    } else {
        assert.equal(assistant.qed(name).committed, true);
        assert.ok(fs.deductions[name]);
    }
    const qedMs = performance.now() - qedStart;
    rules.add(name);
    console.log(JSON.stringify({
        mode, name, node: process.version, tactics: commands.length, applyMs, qedMs,
        heapUsed: process.memoryUsage().heapUsed,
        peakRssBytes: process.resourceUsage().maxRSS * 1024
    }));
}

if (mode === "original") {
    await run("xPerfUnionOriginal", fixture.target, fixture.original);
} else if (mode !== "split") {
    await run("xPerfUnionQuantified", fixture.target, quantified);
} else {
    assert.ok(fixture.target.startsWith("VA:Vc:Vg:"));
    await run("xPerfUnionCore", fixture.target.slice("VA:Vc:Vg:".length),
        ["intros hg hc", ...quantified.slice(1)]);
    await run("xPerfUnionGeneralized", fixture.target, ["intros A c g", "exact xPerfUnionCore"]);
}
