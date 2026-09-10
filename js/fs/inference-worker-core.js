import { initFormalSystem } from "./initial.js";
import { SavesParser } from "./savesparser.js";
import { InferenceProofAssistant } from "./proof-assistant.js";
/** Execute isolated expansion or fully validated qed against a GUI snapshot. */
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
    restored.fastmetarules = request.target.kind === "qed"
        ? request.fastMetaRules : "cvuqe><:#zZQRR";
    restored.disabledMetaRules = [...(request.disabledMetaRules ?? [])];
    let qed;
    if (request.target.kind === "qed") {
        const target = request.target;
        if (restored.inferencePages.activeId !== target.pageId) {
            throw new Error("证明助手只能写入启动时的推理表");
        }
        const assistant = new InferenceProofAssistant(restored, target.theorem, {
            pageId: target.pageId,
            history: target.history,
            ruleNames: target.ruleNames,
            fastMetaRules: request.fastMetaRules,
            allowMcpt: target.allowMcpt,
            allowIfft: target.allowIfft,
            allowIfftEu: target.allowIfftEu
        });
        const result = assistant.qed(target.name);
        qed = { committed: true, ...(result.macroName ? { macroName: result.macroName } : {}) };
    }
    else if (request.target.kind === "proposition") {
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
    return { save, deductions, ...(qed ? { qed } : {}) };
}
//# sourceMappingURL=inference-worker-core.js.map