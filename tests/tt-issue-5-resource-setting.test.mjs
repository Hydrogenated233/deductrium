import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { Core } from "../js/tt/core.js";
import { TTGui } from "../js/tt/gui.js";

const previousDocument = globalThis.document;
const previousLocalStorage = Object.getOwnPropertyDescriptor(globalThis, "localStorage");
const previous = {
    scale: Core.semanticResourceScale,
    nbeMaxNodes: Core.semanticNbEMaxNodes,
    elaborationMaxNodes: Core.semanticTypeElaborationMaxNodes,
    synthesisMaxSteps: Core.semanticTypeSynthesisMaxSteps,
    assertionMaxSteps: Core.semanticTypeAssertionMaxSteps,
    assertionMaxNodes: Core.semanticTypeAssertionMaxNodes,
    outputMaxNodes: Core.semanticTypeCheckMaxOutputNodes
};
const stored = new Map([["deductrium-tt-semantic-resource-scale", "3"]]);
const listeners = new Map();
const input = {
    value: "",
    addEventListener(type, listener) {
        listeners.set(type, listener);
    }
};

try {
    globalThis.document = {
        getElementById(id) {
            return id === "semanticResourceScale" ? input : null;
        }
    };
    Object.defineProperty(globalThis, "localStorage", {
        configurable: true,
        value: {
            getItem(key) { return stored.get(key) ?? null; },
            setItem(key, value) { stored.set(key, value); }
        }
    });

    const gui = Object.create(TTGui.prototype);
    gui.semanticResourceScale = 1;
    gui.skipRendering = false;
    gui.tacticDefinitionsRevision = 7;
    gui.assistWorkerSessionReady = true;
    gui.tacticRequestId = 10;
    gui.unlockedTypes = new Set(["True"]);
    gui.disableSimpleFn = false;
    gui.disableSimpleEq = false;
    gui.inferDisplayMode = "_";
    let revalidations = 0;
    let busy = true;
    gui.revalidateTheorems = () => { revalidations++; };
    gui.setTacticBusy = value => { busy = value; };

    gui.initializeSemanticResourceScale();
    assert.equal(gui.semanticResourceScale, 3,
        "the persisted semantic resource multiplier must be restored on startup");
    assert.equal(input.value, "3");
    assert.equal(gui.getWorkerSystemConfig().semanticResourceScale, 3,
        "the restored multiplier must be included in both Worker configuration paths");

    input.value = "4";
    listeners.get("change")();
    assert.equal(stored.get("deductrium-tt-semantic-resource-scale"), "4");
    assert.equal(Core.semanticTypeAssertionMaxNodes, 8_192);
    assert.equal(revalidations, 1,
        "changing the multiplier must revalidate the theorem chain once");
    assert.equal(gui.assistWorkerSessionReady, false,
        "changing the multiplier must invalidate the active proof-assistant Worker session");
    assert.equal(gui.tacticDefinitionsRevision, -1,
        "the next proof command must replay its history under the new multiplier");
    assert.equal(gui.tacticRequestId, 11,
        "an in-flight proof command must not commit after the resource policy changes");
    assert.equal(busy, false);

    const html = readFileSync(new URL("../index.html", import.meta.url), "utf8");
    assert.match(html, /id="semanticResourceScale"[^>]*type="number"[^>]*min="1"[^>]*max="64"/,
        "the UI must expose the same finite resource multiplier range");
} finally {
    if (previousDocument === undefined) delete globalThis.document;
    else globalThis.document = previousDocument;
    if (previousLocalStorage) {
        Object.defineProperty(globalThis, "localStorage", previousLocalStorage);
    } else {
        delete globalThis.localStorage;
    }
    Core.semanticResourceScale = previous.scale;
    Core.semanticNbEMaxNodes = previous.nbeMaxNodes;
    Core.semanticTypeElaborationMaxNodes = previous.elaborationMaxNodes;
    Core.semanticTypeSynthesisMaxSteps = previous.synthesisMaxSteps;
    Core.semanticTypeAssertionMaxSteps = previous.assertionMaxSteps;
    Core.semanticTypeAssertionMaxNodes = previous.assertionMaxNodes;
    Core.semanticTypeCheckMaxOutputNodes = previous.outputMaxNodes;
}

console.log("GitHub issue #5 resource-setting UI regression passed");
