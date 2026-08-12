import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { markExplicitAtSyntax } from "../js/tt/presentation.js";

const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: ["True", "eq", "eq.rfl"],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});
const parser = new ASTParser();

const log = console.log;
const capturedLogs = [];
console.log = (...args) => capturedLogs.push(args.map(String).join(" "));
try {
    const explicitAtError = engine.check("(@refl _ _ true) true");
    assert.equal(explicitAtError.ok, false, "the explicit @ error fixture must remain ill-typed");
    assert.match(
        explicitAtError.error ?? "",
        /@refl/,
        "error output must preserve an @ alias explicitly written by the user"
    );
    assert.match(
        explicitAtError.error ?? "",
        /_ _ true/,
        "error output must retain the user's explicit argument spelling"
    );

    const implicitAtError = engine.check("(refl true) true");
    assert.equal(implicitAtError.ok, false, "the implicit alias error fixture must remain ill-typed");
    assert.doesNotMatch(
        implicitAtError.error ?? "",
        /@(?:[A-Za-z_][A-Za-z0-9_']*|[0-9]+)/,
        "error output must not expose an automatically generated @ alias"
    );

    const wireAst = JSON.parse(JSON.stringify(
        markExplicitAtSyntax(parser.parse("(@refl _ _ true) true"))
    ));
    const roundTripError = engine.checkAst(wireAst);
    assert.match(
        roundTripError.error ?? "",
        /@refl _ _ true/,
        "Worker JSON round-trip must retain explicit @ presentation metadata"
    );

    engine.core.error({ type: "whnf", name: "" }, "probe", false);
    assert.equal(
        capturedLogs.at(-1),
        "whnf probe",
        "internal semantic nodes must not produce an undefined error-log prefix"
    );
} finally {
    console.log = log;
}

console.log("error presentation regression passed");
