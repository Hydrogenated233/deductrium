import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const engine = new TTAssistEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

const options = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};

engine.start("isSet nat", options);
const expanded = engine.apply("expand isSet");
const expandedFreeVars = Core.getFreeVars(expanded.goals[0].type);
assert.equal(
    expandedFreeVars.has("x'") || expandedFreeVars.has("y'"),
    false,
    "expanding isSet must not expose the definition's alpha-renamed free variables"
);

const introduced = engine.apply("intros n m p q");
assert.deepEqual(
    introduced.goals[0].context.map(([name]) => name),
    ["q", "p", "m", "n"],
    "intros must retain all four dependent binders"
);
assert.equal(
    parser.stringify(introduced.goals[0].type),
    "(p=q)",
    "isSet nat must reduce to the equality of the two equality proofs"
);

const beforeFailure = introduced;
assert.throws(() => engine.apply("expand doesNotExist"), /未找到任何指定展开的项/);
const afterFailure = engine.apply("change (p=q)");
assert.deepEqual(
    afterFailure.goals.map(goal => ({
        type: parser.stringify(goal.type),
        context: goal.context.map(([name]) => name)
    })),
    beforeFailure.goals.map(goal => ({
        type: parser.stringify(goal.type),
        context: goal.context.map(([name]) => name)
    })),
    "a failed expansion must roll back the goal and its dependent context"
);

console.log("GitHub issue #51 isSet expansion regression passed");
