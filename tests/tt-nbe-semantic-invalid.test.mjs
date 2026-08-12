import assert from "node:assert/strict";

import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

const core = engine.core;
for (const [source, expectedError] of [
        ["doesNotExist", /未知的变量/],
        ["true true", /非函数尝试作用/],
        ["succ true", /函数作用类型不匹配/]
    ]) {
        const result = engine.check(source);
        assert.equal(result.ok, false, `${source} must be rejected`);
        assert.match(result.error ?? "", expectedError,
            `${source} must report the semantic error in Chinese`);
}

console.log("pure NbE semantic-invalid regression passed");
