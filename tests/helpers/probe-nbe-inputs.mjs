import { TTCoreEngine } from "../../js/tt/engine.js";
import { initTypeSystem } from "../../js/tt/initial.js";

const inputs = process.argv.slice(2);
const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

for (const source of inputs) {
    const result = engine.check(source);
    console.log(JSON.stringify({
        source,
        ok: result.ok,
        error: result.error,
        semanticFastPath: result.ok
    }));
}
