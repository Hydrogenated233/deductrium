import assert from "node:assert/strict";

import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const creativeRuleIds = [...new Set(initTypeSystem().map(rule => rule.id))];
assert.ok(creativeRuleIds.includes("sorry"));

const creative = new TTCoreEngine();
creative.configure({
    unlockedTypes: creativeRuleIds,
    inferDisplayMode: "_",
    language: "zh"
});
const creativeFalse = creative.check("false");
assert.equal(creativeFalse.ok, true, creativeFalse.error);
assert.equal(creativeFalse.type?.type, "var");
assert.equal(creativeFalse.type?.name, "False");

const survival = new TTCoreEngine();
survival.configure({
    unlockedTypes: ["True", "False"],
    disableSimpleFn: true,
    disableSimpleEq: true,
    inferDisplayMode: "_",
    language: "zh"
});
const survivalFalse = survival.check("false");
assert.equal(survivalFalse.ok, false);
assert.match(survivalFalse.error ?? "", /未知的变量：false/);

const options = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};
const creativeAssist = new TTAssistEngine();
creativeAssist.configure({
    unlockedTypes: creativeRuleIds,
    inferDisplayMode: "_",
    language: "zh"
});
creativeAssist.start("True", options);
const closed = creativeAssist.apply("destruct false");
assert.equal(closed.goals.length, 0);
assert.match(creativeAssist.qed().proof, /ind_False/);

const survivalAssist = new TTAssistEngine();
survivalAssist.configure({
    unlockedTypes: ["True", "False"],
    disableSimpleFn: true,
    disableSimpleEq: true,
    inferDisplayMode: "_",
    language: "zh"
});
survivalAssist.start("True", options);
assert.throws(
    () => survivalAssist.apply("destruct false"),
    /未知的变量：false/
);

console.log("creative-only type-theory sorry regression passed");
