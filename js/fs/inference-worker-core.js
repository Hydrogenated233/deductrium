import { initFormalSystem } from "./initial.js";
import { SavesParser } from "./savesparser.js";
/** Execute one isolated inference expansion against a serialized GUI snapshot. */
export function expandInferenceSnapshot(request) {
    if (!request || typeof request.save !== "string" || !request.target) {
        throw new Error("推理层 Worker 请求无效");
    }
    const parsed = JSON.parse(request.save);
    const data = Array.isArray(parsed) ? parsed : parsed?.data;
    if (!Array.isArray(data))
        throw new Error("推理系统存档格式无效");
    const saves = new SavesParser(request.creative);
    const initialized = initFormalSystem(request.creative).fs;
    const restored = saves.deserializeArr(initialized, data).fs;
    restored.fastmetarules = "cvuqe><:#zZQRR";
    if (request.target.kind === "proposition") {
        if (!Number.isInteger(request.target.index) || request.target.index < 0
            || !restored.propositions[request.target.index]) {
            throw new Error("推理表定理不存在");
        }
        restored.expandMacroWithProp(request.target.index);
    }
    else if (request.target.kind === "inline-proposition") {
        if (!Number.isInteger(request.target.index) || request.target.index < 0
            || !restored.propositions[request.target.index]) {
            throw new Error("推理表定理不存在");
        }
        restored.inlineMacroInProp(request.target.index);
    }
    else {
        if (typeof request.target.name !== "string" || !request.target.name) {
            throw new Error("推理规则名称无效");
        }
        restored.expandMacroWithDefaultValue(request.target.name);
    }
    const gui = {
        formalSystem: restored,
        deductions: Object.keys(restored.deductions),
        metarules: request.metarules,
        getProps: () => restored.propositions,
        pageStore: restored.inferencePages
    };
    const save = saves.serialize(gui);
    const deductions = {};
    for (const [name, deduction] of Object.entries(restored.deductions)) {
        deductions[name] = saves.serializeDeduction(deduction);
    }
    return { save, deductions };
}
//# sourceMappingURL=inference-worker-core.js.map