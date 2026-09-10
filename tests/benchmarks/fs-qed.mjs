import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";
import { Worker } from "node:worker_threads";
import { initFormalSystem } from "../../js/fs/initial.js";
import { SavesParser } from "../../js/fs/savesparser.js";
import { InferenceProofAssistant } from "../../js/fs/proof-assistant.js";

const fixture = JSON.parse(readFileSync(new URL("../fixtures/fs-issue-43-common-multiple.json", import.meta.url)));
const data = fixture.save.data;
const fs = new SavesParser(false).deserializeArr(initFormalSystem(false).fs, data).fs;
const page = fs.inferencePages.pages.find(page => page.name === "elV1");
assert.equal(page.propositions.length, 0);
fs.inferencePages.activate(page.id);
const history = fixture.proof.script.split("\n").filter(command => !command.startsWith("qed "));
const assistant = new InferenceProofAssistant(fs, fixture.proof.target, {
    pageId: page.id, ruleNames: data[5], allowMcpt: false
});
let started = performance.now();
for (const command of history) assistant.apply(command);
const tacticsMs = performance.now() - started;
const preview = assistant.materializeQed("xPerfProbe");
assert.equal(assistant.snapshot().complete, true);
started = performance.now();
let commitMs;
let ticks = 0;
let maxTickGapMs = 0;
let lastTick = started;
const timer = setInterval(() => {
    const now = performance.now();
    maxTickGapMs = Math.max(maxTickGapMs, now - lastTick);
    lastTick = now;
    ticks++;
}, 10);
try {
    if (process.argv.includes("--sync")) {
        assistant.commit(preview);
        commitMs = performance.now() - started;
        assert.ok(fs.deductions.xPerfProbe);
        await new Promise(resolve => setTimeout(resolve, 0));
    } else {
        const save = new SavesParser(false).serialize({
            formalSystem: fs, deductions: data[5], metarules: [],
            getProps: () => fs.propositions, pageStore: fs.inferencePages
        });
        const recipe = preview.steps[0].assistant;
        const worker = new Worker(new URL("./fs-qed-worker.mjs", import.meta.url));
        try {
            const result = await new Promise((resolve, reject) => {
                worker.once("message", message => message.error ? reject(new Error(message.error)) : resolve(message));
                worker.once("error", reject);
                worker.once("exit", code => { if (code) reject(new Error(`Worker exited: ${code}`)); });
                worker.postMessage({
                    save, creative: false, fastMetaRules: recipe.fastMetaRules ?? "cvuqe><:#zZQR",
                    metarules: [],
                    target: {
                        kind: "qed", theorem: recipe.theorem, history, pageId: page.id,
                        name: "xPerfProbe", ruleNames: data[5],
                        allowMcpt: false, allowIfft: true, allowIfftEu: true
                    }
                });
            });
            commitMs = performance.now() - started;
            assert.ok(result.deductions.xPerfProbe);
            assert.equal(result.qed?.committed, true);
            assert.equal(fs.deductions.xPerfProbe, undefined, "worker must remain isolated");
        } finally {
            await worker.terminate();
        }
    }
} finally {
    clearInterval(timer);
}
console.log(JSON.stringify({
    mode: process.argv.includes("--sync") ? "sync" : "worker",
    node: process.version, tacticCount: history.length, tacticsMs, commitMs,
    ticks, maxTickGapMs, peakRssBytes: process.resourceUsage().maxRSS * 1024
}, null, 2));
