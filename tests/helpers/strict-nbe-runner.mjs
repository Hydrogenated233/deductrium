import * as coreModule from "../../js/tt/core.js";

const { Core } = coreModule;
const InferTable = coreModule.InferTable;

const tests = process.argv.slice(2);
if (!tests.length) throw new Error("strict-nbe-runner requires at least one test module");

const blockedCoreMethods = [
    "check",
    "equal",
    "reduce",
    "whnf",
    "registConstType",
    "checkConst",
    "markAndCheckInferedValue",
    "addInferRel",
    "solveInferDefered",
    "solveInferRel",
    "fillInfered"
];
const blockedInferTableMethods = [
    "addNewName",
    "clone",
    "snapshot",
    "findInferVal"
];

for (const name of blockedCoreMethods) {
    blockMethodIfPresent(Core?.prototype, name, `Core.${name}`);
}
if (InferTable) {
    for (const name of blockedInferTableMethods) {
        blockMethodIfPresent(InferTable.prototype, name, `InferTable.${name}`);
    }
    blockMethodIfPresent(InferTable, "fromSnapshot", "InferTable.fromSnapshot");
}

for (const test of tests) {
    try {
        await import(new URL(`../${test}`, import.meta.url));
        console.log(`[STRICT-NBE PASS] ${test}`);
    } catch (error) {
        console.error(`[STRICT-NBE FAIL] ${test}`);
        console.error(error?.stack ?? error);
        process.exit(1);
    }
}

function blockMethodIfPresent(target, name, label) {
    if (typeof target?.[name] !== "function") return;
    target[name] = function () {
        throw new Error(`[STRICT-NBE] legacy ${label}\n${new Error().stack}`);
    };
}
