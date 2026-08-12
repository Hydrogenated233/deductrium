import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const session = new TTCoreSession();
session.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

const equivalence = parser.parse(
    "I_eqv_True:=(pair (λf:(I→True).((Σg:(True→I),(Πx:I,(x=(g (f x)))))×"
    + "(Σh:(True→I),(Πx:True,(x=(f (h x))))))) (λh:I.true) ((pair "
    + "(λg:(True→I).(Πx:I,(x=(g ((λh:I.true) x))))) (λh:True.0I) "
    + "(λx:I.ind_I (λx:I.(x=((λh:True.0I) ((λh:I.true) x)))) rfl "
    + "(inveq segI) ((transleft segI rfl)▪((rightrfl (inveq segI))▪rfl)) x)),"
    + "(pair (λh:(True→I).(Πx:True,(x=((λh:I.true) (h x))))) (λh:True.0I) "
    + "(λx:True.ind_True (λx:True.(x=((λh:I.true) ((λh:True.0I) x)))) rfl x)))):"
    + "(I≃True)"
);

const originalLog = console.log;
try {
    console.log = () => { };
    const registered = session.validate(0, equivalence);
    assert.equal(registered.ok, true, registered.error);

    const assist = new TTAssistEngine(session.engine);
    const options = {
        disableMultipleApply: false,
        disableDestructConds: false,
        disableDestructEq: false
    };
    assist.start("isProp I", options);
    const afterRewrite = assist.apply("rw (ua I_eqv_True)");
    assert.equal(afterRewrite.goals.length, 1);
    assert.match(parser.stringify(afterRewrite.goals[0].type), /True/);
} finally {
    console.log = originalLog;
}

console.log("proof-assistant semantic-cache rewrite regression passed");
