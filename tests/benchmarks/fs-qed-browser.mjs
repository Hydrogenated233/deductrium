import assert from "node:assert/strict";
import { createServer } from "node:http";
import { readFile, writeFile } from "node:fs/promises";
import { resolve, sep, extname } from "node:path";
import { fileURLToPath } from "node:url";
import { withHeadlessBrowser, evaluate } from "./browser-cdp.mjs";

// A fresh browser profile and an ephemeral origin, with only the real FS GUI
// bootstrapped. No game, autosave, existing tab or player storage is touched.
const root = fileURLToPath(new URL("../../", import.meta.url));
const index = (await readFile(new URL("../../index.html", import.meta.url), "utf8"))
    .replace(/<script type="module" src="js\/game\.js">\s*<\/script>/, "");
const server = createServer(async (request, response) => {
    try {
        const name = decodeURIComponent(new URL(request.url, "http://localhost").pathname);
        const path = resolve(root, "." + name);
        if (path !== resolve(root) && !path.startsWith(resolve(root) + sep)) {
            response.writeHead(403).end();
            return;
        }
        const body = name === "/" ? index : await readFile(path);
        response.setHeader("Content-Type", name === "/" ? "text/html; charset=utf-8"
            : ({ ".js": "text/javascript", ".json": "application/json", ".css": "text/css" })[extname(path)]
                ?? "application/octet-stream");
        response.end(body);
    } catch {
        response.writeHead(404).end();
    }
});
await new Promise(resolve => server.listen(0, "127.0.0.1", resolve));
const origin = `http://127.0.0.1:${server.address().port}`;
try {
    await withHeadlessBrowser(async cdp => {
        const { targetId } = await cdp.command("Target.createTarget", { url: "about:blank" });
        const { sessionId } = await cdp.command("Target.attachToTarget", { targetId, flatten: true });
        await cdp.command("Page.enable", {}, sessionId);
        await cdp.command("Runtime.enable", {}, sessionId);
        await cdp.command("Emulation.setDeviceMetricsOverride", {
            width: 1280, height: 900, deviceScaleFactor: 1, mobile: false
        }, sessionId);
        await cdp.command("Page.navigate", { url: origin }, sessionId);
        await waitFor(cdp, sessionId, "!!document.getElementById('fs-proof-script')");
        await evaluate(cdp, sessionId, `(async () => {
            const { FSGui } = await import('/js/fs/gui.js');
            const { SavesParser } = await import('/js/fs/savesparser.js');
            const fixture = await (await fetch('/tests/fixtures/fs-issue-43-common-multiple.json')).json();
            const gui = window.testGui = new FSGui(
                ...['prop-list','deduct-list','meta-list','sysfn-list','action-input','hint','display-p-layer']
                    .map(id => document.getElementById(id)),
                document.querySelectorAll('.cmd-btns button'), false, true
            );
            new SavesParser(false).deserialize(gui, JSON.stringify(fixture.save));
            gui.formalSystem.fastmetarules = 'c>:<qvue';
            gui.skipRendering = false;
            gui.activateInferencePage(gui.pageStore.pages.find(p => p.name === 'elV1').id);
            document.getElementById('panel').classList.remove('hide');
            for (const panel of document.querySelectorAll('#panel>div')) panel.classList.remove('show');
            document.getElementById('panel-1').classList.add('show');
            document.getElementById('loading').remove();
            document.getElementById('gamemode').textContent = '[FS benchmark]';
            window.prepare = name => {
                gui.startInferenceProofAssistant(fixture.proof.target);
                if (!gui.inferenceProofTextMode) gui.toggleInferenceProofTextMode();
                const script = document.getElementById('fs-proof-script');
                script.value = fixture.proof.script.replace(/qed [^\\n]+/, 'qed ' + name);
                gui.inferenceProofScript = script.value;
                script.selectionStart = script.selectionEnd = script.value.length;
                gui.inferenceProofScriptEditor.refresh();
                document.getElementById('fs-proof-assistant').scrollIntoView();
            };
            window.workerCalls = 0;
            window.phaseTimes = [];
            for (const name of ['inferenceQedFingerprint', 'inferenceWorkerSave',
                'applyInferenceWorkerResult', 'updatePropositionList', 'updateDeductionList']) {
                const original = gui[name];
                gui[name] = function(...args) {
                    const start = performance.now();
                    try { return original.apply(this, args); }
                    finally { phaseTimes.push({ name, ms: performance.now() - start }); }
                };
            }
            const NativeWorker = window.Worker;
            window.Worker = class extends NativeWorker {
                postMessage(...args) { window.workerCalls++; return super.postMessage(...args); }
            };
            window.prepare('xBrowserCancelled');
        })()`);
        await evaluate(cdp, sessionId, "document.getElementById('fs-proof-script-run').click()");
        await waitFor(cdp, sessionId, "window.workerCalls === 1");
        const beforeCancel = await evaluate(cdp, sessionId, `({
            busy: testGui.inferenceProofBusy,
            disabled: document.getElementById('fs-proof-script-run').disabled,
            cancel: document.getElementById('fs-proof-close').textContent
        })`);
        assert.equal(beforeCancel.busy, true);
        assert.equal(beforeCancel.disabled, true);
        await evaluate(cdp, sessionId, "document.getElementById('fs-proof-close').click()");
        await waitFor(cdp, sessionId, "!testGui.inferenceProofBusy");
        assert.equal(await evaluate(cdp, sessionId,
            "!!testGui.inferenceProofAssistant && !testGui.formalSystem.deductions.xBrowserCancelled"), true);
        await evaluate(cdp, sessionId, `(() => {
            window.prepare('xBrowserCommonMultiple');
            phaseTimes.length = 0;
            window.metrics = { ticks: 0, maxGapMs: 0, longTasks: [], started: performance.now() };
            let last = performance.now();
            window.tickTimer = setInterval(() => {
                const now = performance.now();
                metrics.maxGapMs = Math.max(metrics.maxGapMs, now - last);
                last = now; metrics.ticks++;
            }, 10);
            window.observer = new PerformanceObserver(list => {
                metrics.longTasks.push(...list.getEntries().map(e => e.duration));
            });
            observer.observe({ type: 'longtask' });
            document.getElementById('fs-proof-script-run').click();
        })()`);
        await waitFor(cdp, sessionId, "window.workerCalls === 2");
        await cdp.command("Page.captureScreenshot", { format: "png" }, sessionId).then(async screenshot => {
            if (process.env.FS_QED_SCREENSHOT) {
                await writeFile(process.env.FS_QED_SCREENSHOT, Buffer.from(screenshot.data, "base64"));
            }
        });
        // An explicit second run while busy must not dispatch again.
        await evaluate(cdp, sessionId, "testGui.replayInferenceProofText(true, false)");
        assert.equal(await evaluate(cdp, sessionId, "window.workerCalls"), 2);
        await waitFor(cdp, sessionId, "!testGui.inferenceProofBusy", 120_000);
        const result = await evaluate(cdp, sessionId, `(() => {
            clearInterval(tickTimer); observer.disconnect();
            return {
                ...metrics, elapsedMs: performance.now() - metrics.started,
                phaseTimes,
                workerCalls,
                saved: !!testGui.formalSystem.deductions.xBrowserCommonMultiple,
                assistantClosed: testGui.inferenceProofAssistant === null,
                pages: testGui.pageStore.pages.map(p => ({ name: p.name, rows: p.propositions.length })),
                error: document.getElementById('fs-proof-errmsg').textContent
            };
        })()`);
        assert.equal(result.saved, true, JSON.stringify(result));
        assert.equal(result.assistantClosed, true);
        assert.equal(result.pages.find(p => p.name === "bigpack").rows, 38);
        assert.equal(result.workerCalls, 2);
        assert.ok(result.ticks > 0, "event loop must run while worker validates");
        console.log(JSON.stringify(result, null, 2));
    });
} finally {
    server.closeAllConnections();
    await new Promise(resolve => server.close(resolve));
}

async function waitFor(cdp, sessionId, expression, timeout = 30_000) {
    const end = Date.now() + timeout;
    while (!await evaluate(cdp, sessionId, expression)) {
        if (Date.now() >= end) throw new Error(`Timed out: ${expression}`);
        await new Promise(resolve => setTimeout(resolve, 50));
    }
}
