import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
};
const options = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};

const cases = [
    { command: "exact refl true", proof: "(refl true)" },
    { command: "exact @refl _ _ true", proof: "(@refl _ True true)" },
    { command: "apply refl true", proof: "(refl true)" },
    { command: "apply @refl _ _ true", proof: "(@refl _ True true)" },
    {
        target: "(true=true)×(true=true)",
        command: "exact (@refl _ _ true,refl true)",
        proof: "((@refl _ True true),(refl true))"
    },
    {
        target: "(true=true)×(true=true)",
        command: "exact (@refl _ _ true,refl _)",
        proof: "((@refl _ True true),(refl true))"
    }
];

const originalLog = console.log;
try {
    console.log = () => { };
    for (const testCase of cases) {
        const engine = new TTAssistEngine();
        engine.configure(config);
        const snapshot = engine.start(testCase.target ?? "true=true", options);
        assert.equal(snapshot.goals.length, 1);
        const completed = engine.apply(testCase.command);
        assert.equal(completed.goals.length, 0);
        assert.equal(engine.qed().proof, testCase.proof,
            "QED must preserve the user's alias or explicit @ spelling");
    }

    const applyEngine = new TTAssistEngine();
    applyEngine.configure(config);
    applyEngine.start("Πf:(true=true)→(true=true)→False,False", options);
    applyEngine.apply("intro f");
    const afterApply = applyEngine.apply("apply f");
    assert.deepEqual(afterApply.goals.map(goal => parser.stringify(goal.type)), [
        "(true=true)",
        "(true=true)"
    ]);
    const afterExplicitExact = applyEngine.apply("exact @refl _ _ true");
    assert.equal(
        parser.stringify(afterExplicitExact.elem),
        "(λf:((true=true)→((true=true)→False)).f (@refl _ True true) (?#0))",
        "an explicit @ occurrence must survive while a same-name unresolved position stays compact"
    );
    applyEngine.apply("exact refl _");
    assert.equal(
        applyEngine.qed().proof,
        "(λf:((true=true)→((true=true)→False)).f (@refl _ True true) (refl true))",
        "apply must preserve explicit @ and implicit underscore spelling per occurrence"
    );

    const rewriteEngine = new TTAssistEngine();
    rewriteEngine.configure(config);
    rewriteEngine.start("Πp:true=true,true=true", options);
    rewriteEngine.apply("intro p");
    const afterRewrite = rewriteEngine.apply("rw (@inveq _ _ _ _ p)");
    assert.equal(
        parser.stringify(afterRewrite.elem),
        "(λp:(true=true).trans (λx:True.(x=x)) (inveq (@inveq _ True true true p)) (?#0))",
        "rw must keep only the user-written @inveq explicit"
    );
    assert.equal(parser.stringify(afterRewrite.goals[0].type), "(true=true)");
    rewriteEngine.apply("exact refl _");
    assert.equal(
        rewriteEngine.qed().proof,
        "(λp:(true=true).trans (λx:True.(x=x)) (inveq (@inveq _ True true true p)) (refl true))",
        "rw must preserve occurrence-specific @ and underscore spelling through QED"
    );

    const sugarRewriteEngine = new TTAssistEngine();
    sugarRewriteEngine.configure(config);
    sugarRewriteEngine.start(
        "Πa:U,Πx:a,Πy:a,Πp:(x=y),(refl x)=(p*inveq p)",
        options
    );
    for (const command of ["intro a", "intro x", "intro y", "intro p"]) {
        sugarRewriteEngine.apply(command);
    }
    const sugarRewrite = sugarRewriteEngine.apply("rw p");
    const rewrittenGoal = parser.stringify(sugarRewrite.goals[0].type);
    assert.match(rewrittenGoal, /=/,
        "rw must keep equality notation in the displayed goal");
    assert.match(rewrittenGoal, /▪/,
        "rw must keep path-composition notation in the displayed goal");
    assert.doesNotMatch(rewrittenGoal, /\beq\b|\bcompeq\b/,
        "rw must not expose internal equality or composition constants");
} finally {
    console.log = originalLog;
}

console.log("proof-assistant surface presentation regression passed");
