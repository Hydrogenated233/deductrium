import { AssertionSystem } from "./assertion.js";
import { ASTParser } from "./astparser.js";
import { DEFERRED_ASSISTANT_STEP } from "./formalsystem.js";
import { initFormalSystem } from "./initial.js";
import { RuleParser } from "./metarule.js";
import { TR } from "../lang.js";
// Ensure the synchronous replay hook is registered for CLI save consumers too;
// the GUI is not necessarily imported by callers of SavesParser.
import "./proof-assistant.js";
const FS_SAVE_FORMAT_VERSION = 2;
const astparser = new ASTParser;
export class SavesParser {
    creative = false;
    constructor(creative) {
        this.creative = creative;
        this.bug260616fixer.fixbug260616 = true;
    }
    serializeDeductionStep(s) {
        const tuple = [
            s.deductionIdx, s.conditionIdxs,
            s.replaceValues.map(v => astparser.stringifyTight(v))
        ];
        if (s.assistant)
            tuple[3] = this.serializeAssistantPayload(s.assistant);
        if (s.info !== undefined)
            tuple[4] = s.info;
        return tuple;
    }
    serializeProposition(p) {
        const value = astparser.stringifyTight(p.value);
        const step = p.from ? this.serializeDeductionStep(p.from) : null;
        return p.deferredKind ? [value, step, p.deferredKind] : [value, step];
    }
    deserializeDeductionStep(v) {
        const assistant = v[3] ? this.deserializeAssistantPayload(v[3]) : undefined;
        return {
            conditionIdxs: v[1],
            deductionIdx: v[0],
            replaceValues: v[2].map(v => astparser.parse(v)),
            ...(v[4] !== undefined ? { info: v[4] } : {}),
            ...(assistant ? { assistant } : {})
        };
    }
    serializeAssistantPayload(payload) {
        return {
            kind: "assistant",
            version: 1,
            pageId: payload.pageId,
            theorem: astparser.stringifyTight(payload.theorem),
            history: [...payload.history],
            ...(payload.ruleNames ? { ruleNames: [...payload.ruleNames] } : {}),
            ...(payload.fastMetaRules !== undefined ? { fastMetaRules: payload.fastMetaRules } : {}),
            ...(payload.allowMcpt !== undefined ? { allowMcpt: payload.allowMcpt } : {}),
            ...(payload.tauto ? { tauto: { checkedTheorem: astparser.stringifyTight(payload.tauto.checkedTheorem) } } : {}),
            premises: payload.premises.map(premise => ({
                ...(premise.pageId ? { pageId: premise.pageId } : {}),
                index: premise.index,
                value: astparser.stringifyTight(premise.value)
            }))
        };
    }
    deserializeAssistantPayload(payload) {
        if (!payload || payload.kind !== "assistant" || payload.version !== 1
            || typeof payload.pageId !== "string" || typeof payload.theorem !== "string"
            || !Array.isArray(payload.history) || !payload.history.every(v => typeof v === "string")
            || (payload.ruleNames !== undefined
                && (!Array.isArray(payload.ruleNames) || !payload.ruleNames.every(v => typeof v === "string")))
            || (payload.fastMetaRules !== undefined && typeof payload.fastMetaRules !== "string")
            || (payload.allowMcpt !== undefined && typeof payload.allowMcpt !== "boolean")
            || (payload.tauto !== undefined && (!payload.tauto
                || typeof payload.tauto.checkedTheorem !== "string"))
            || !Array.isArray(payload.premises)) {
            throw TR("证明助手延迟步骤存档格式无效");
        }
        try {
            const premises = payload.premises.map(premise => {
                if (!premise || (premise.pageId !== undefined && typeof premise.pageId !== "string")
                    || !Number.isInteger(premise.index) || premise.index < 0
                    || typeof premise.value !== "string")
                    throw new Error("invalid premise");
                return {
                    ...(premise.pageId !== undefined ? { pageId: premise.pageId } : {}),
                    index: premise.index,
                    value: astparser.parse(premise.value)
                };
            });
            return {
                kind: "assistant",
                version: 1,
                pageId: payload.pageId,
                theorem: astparser.parse(payload.theorem),
                history: [...payload.history],
                ...(payload.ruleNames ? { ruleNames: [...payload.ruleNames] } : {}),
                ...(payload.fastMetaRules !== undefined ? { fastMetaRules: payload.fastMetaRules } : {}),
                ...(payload.allowMcpt !== undefined ? { allowMcpt: payload.allowMcpt } : {}),
                ...(payload.tauto ? { tauto: { checkedTheorem: astparser.parse(payload.tauto.checkedTheorem) } } : {}),
                premises
            };
        }
        catch {
            throw TR("证明助手延迟步骤存档格式无效");
        }
    }
    deserializeProposition(v) {
        const deferredKind = v[2] === "cpt" || v[2] === "assistant" ? v[2] : undefined;
        return {
            value: astparser.parse(v[0]),
            from: v[1] ? this.deserializeDeductionStep(v[1]) : null,
            ...(deferredKind ? { deferredKind } : {})
        };
    }
    serializeDeduction(deduction) {
        const value = astparser.stringifyTight(deduction.value);
        const isDeferredCpt = deduction.deferredKind === "cpt";
        const isDeferredAssistant = deduction.deferredKind === "assistant";
        const steps = isDeferredCpt || isDeferredAssistant ? undefined : deduction.steps?.map(s => this.serializeDeductionStep(s));
        const tempvars = isDeferredCpt || isDeferredAssistant ? undefined : (deduction.tempvars?.size ? Array.from(deduction.tempvars) : undefined);
        if (isDeferredCpt)
            return [value, deduction.from, steps, tempvars, "cpt"];
        if (isDeferredAssistant) {
            const payload = deduction.deferredPayload;
            if (!payload)
                throw TR("证明助手延迟步骤缺少操作序列");
            return [value, deduction.from, steps, tempvars, "assistant", this.serializeAssistantPayload(payload)];
        }
        // if fs has tempvars record, then serialize it
        return tempvars ? [value, deduction.from, steps, tempvars] : [value, deduction.from, steps];
    }
    // 26-3-30: bug fix: rule "<.a1_n" not exist, use ":c{rec},.cs" instead
    fixbug260330_(num) {
        return num === 3 ? ":ca1,.cs" : (":c" + this.fixbug260330_(num - 1) + ",.cs");
    }
    fixbug260330(s) {
        const match = s.match(/>\.a1\_([1-9][0-9]*)$/);
        if (!match)
            return s;
        const num = Number(match[1]);
        return s.replace(/>\.a1\_([1-9][0-9]*)$/, this.fixbug260330_(num));
    }
    // rule :.=t is invalid but can be generated   ==convert it to==>   :.=t,.=t
    // use a wrong version parser to generate 
    bug260616fixer = new RuleParser;
    ruleparser = new RuleParser;
    fixbug260616(s) {
        if (s.split(":").length > s.split(",").length || s.split(":").length < s.split(",").length) {
            try {
                this.ruleparser.parse(s);
            }
            catch (e) {
                return this.bug260616fixer.stringify(this.bug260616fixer.parse(s));
            }
            return s;
        }
        return s;
    }
    assert = new AssertionSystem;
    deserializeDeduction(name, fs, sd) {
        // deserialized data is reliable, no need to regen tempvars
        // fix bugs for nested #nf funcs 26-7-5
        const val = astparser.parse(sd[0]);
        try {
            this.assert.expand(val, false);
        }
        catch (e) { }
        const deferredKind = sd[4] === "cpt" || sd[4] === "assistant" ? sd[4] : undefined;
        fs.addDeduction(name, val, sd[1], deferredKind ? undefined : sd[2]?.map(e => ({
            deductionIdx: e[0].includes(">.a1_") ? this.fixbug260330(e[0]) : e[0].includes(":") ? this.fixbug260616(e[0]) : e[0],
            conditionIdxs: e[1],
            replaceValues: e[2].map(v => astparser.parse(v)),
            ...(e[4] !== undefined ? { info: e[4] } : {}),
            ...(e[3] ? { assistant: this.deserializeAssistantPayload(e[3]) } : {})
        })), deferredKind ? new Set() : (sd[3] ? new Set(sd[3]) : new Set()));
        if (deferredKind)
            fs.deductions[name].deferredKind = deferredKind;
        if (deferredKind === "assistant") {
            const payload = sd[5];
            if (!payload || payload.kind !== "assistant" || payload.version !== 1
                || typeof payload.pageId !== "string" || typeof payload.theorem !== "string"
                || !Array.isArray(payload.history) || !payload.history.every(v => typeof v === "string")
                || (payload.ruleNames !== undefined
                    && (!Array.isArray(payload.ruleNames) || !payload.ruleNames.every(v => typeof v === "string")))
                || (payload.fastMetaRules !== undefined && typeof payload.fastMetaRules !== "string")
                || (payload.allowMcpt !== undefined && typeof payload.allowMcpt !== "boolean")
                || (payload.tauto !== undefined && (!payload.tauto
                    || typeof payload.tauto.checkedTheorem !== "string"))
                || !Array.isArray(payload.premises)) {
                throw TR("证明助手延迟步骤存档格式无效");
            }
            try {
                const premises = payload.premises.map(premise => {
                    if (!premise || (premise.pageId !== undefined && typeof premise.pageId !== "string")
                        || !Number.isInteger(premise.index) || premise.index < 0
                        || typeof premise.value !== "string")
                        throw new Error("invalid premise");
                    return {
                        ...(premise.pageId !== undefined ? { pageId: premise.pageId } : {}),
                        index: premise.index,
                        value: astparser.parse(premise.value)
                    };
                });
                fs.deductions[name].deferredPayload = {
                    kind: "assistant",
                    version: 1,
                    pageId: payload.pageId,
                    theorem: astparser.parse(payload.theorem),
                    history: [...payload.history],
                    ...(payload.ruleNames ? { ruleNames: [...payload.ruleNames] } : {}),
                    ...(payload.fastMetaRules !== undefined ? { fastMetaRules: payload.fastMetaRules } : {}),
                    ...(payload.allowMcpt !== undefined ? { allowMcpt: payload.allowMcpt } : {}),
                    ...(payload.tauto ? { tauto: { checkedTheorem: astparser.parse(payload.tauto.checkedTheorem) } } : {}),
                    premises
                };
            }
            catch {
                throw TR("证明助手延迟步骤存档格式无效");
            }
        }
    }
    serialize(gui) {
        const fs = gui.formalSystem;
        const dlist = gui.deductions;
        const userD = {};
        for (const [n, d] of Object.entries(fs.deductions)) {
            if (n === DEFERRED_ASSISTANT_STEP)
                continue;
            // save a..x
            if (!d.from.endsWith("*") && !n.endsWith("x"))
                continue;
            if (n.startsWith("c") || n.startsWith("<") || n.startsWith(">") || n.startsWith("v") || n.startsWith("u") || n.startsWith("e") || n.startsWith(".")) {
                continue;
            }
            userD[n] = this.serializeDeduction(d);
        }
        const props = gui.getProps();
        // The GUI adapter may expose a page store of its own while older
        // callers only know about FormalSystem.  Keep both views coherent at
        // the save boundary and always persist the active page's live input.
        const pageStore = gui.pageStore ?? fs.inferencePages;
        const cmd = gui.cmd;
        if (pageStore.active) {
            pageStore.active.propositions = cmd?.cmdBuffer?.[0] === "entr" && Array.isArray(cmd.cmdBuffer[2])
                ? cmd.cmdBuffer[2]
                : fs.propositions;
            const input = gui.actionInput?.value;
            if (typeof input === "string" || cmd) {
                const previousState = pageStore.active.command.state && typeof pageStore.active.command.state === "object"
                    ? pageStore.active.command.state
                    : {};
                pageStore.setCommandSnapshot({
                    input: typeof input === "string" ? input : pageStore.active.command.input,
                    buffer: cmd?.cmdBuffer?.slice?.() ?? pageStore.active.command.buffer,
                    state: cmd ? {
                        ...previousState,
                        escClear: cmd.escClear,
                        lastDeduction: cmd.lastDeduction,
                        hint: gui.hintText?.innerHTML
                    } : pageStore.active.command.state
                });
            }
        }
        const pagePayload = {
            activeId: pageStore.activeId,
            pages: pageStore.pages.map(page => ({
                id: page.id,
                name: page.name,
                propositions: page.propositions.map(s => this.serializeProposition(s)),
                command: {
                    input: page.command.input,
                    buffer: page.command.buffer,
                    state: page.command.state
                }
            }))
        };
        return JSON.stringify({
            version: FS_SAVE_FORMAT_VERSION,
            data: [
                Array.from(fs.consts), Array.from(fs.fns), Array.from(fs.verbs),
                [[ /* todo metamacro */], ...gui.metarules], userD, dlist,
                props.map(s => this.serializeProposition(s)),
                pagePayload
            ]
        });
    }
    deserializeArr(fs, arr) {
        // 
        if (arr.length < 7)
            arr.splice(2, 0, [], []);
        const [arrC, arrFn, arrVb, arrM, dictD, arrD, arrP, pagePayload] = arr;
        for (const v of arrC) {
            fs.consts.add(v);
        }
        for (const v of arrFn) {
            fs.fns.add(v);
        }
        for (const v of arrVb) {
            fs.verbs.add(v);
        }
        for (const [k, v] of Object.entries(dictD)) {
            if (v.length)
                this.deserializeDeduction(k, fs, v);
        }
        if (pagePayload !== undefined) {
            if (!pagePayload || typeof pagePayload !== "object"
                || !Array.isArray(pagePayload.pages) || pagePayload.pages.length === 0
                || typeof pagePayload.activeId !== "string") {
                throw TR("推理表存档格式无效");
            }
            const pages = pagePayload.pages.map((page) => {
                if (!page || typeof page.id !== "string" || typeof page.name !== "string"
                    || !Array.isArray(page.propositions)
                    || (page.command !== undefined && (!page.command || typeof page.command !== "object"
                        || (page.command.input !== undefined && typeof page.command.input !== "string")
                        || (page.command.buffer !== undefined && !Array.isArray(page.command.buffer))))) {
                    throw TR("推理表存档格式无效");
                }
                return {
                    id: page.id,
                    name: page.name,
                    propositions: page.propositions.map(v => this.deserializeProposition(v)),
                    command: {
                        input: page.command?.input ?? "",
                        buffer: page.command?.buffer ?? [],
                        state: page.command?.state
                    }
                };
            });
            if (!pages.some(page => page.id === pagePayload.activeId)) {
                throw TR("推理表存档格式无效");
            }
            fs.restoreInferencePages({ pages, activeId: pagePayload.activeId });
        }
        else if (arrP)
            for (const v of arrP) {
                fs.propositions.push(this.deserializeProposition(v));
            }
        return { fs, arrD, arrM };
    }
    deserializeMetaMacro(gui, arr) {
        // todo
        gui.formalSystem.metaMacro = {};
    }
    deserialize(gui, str) {
        // Parse and validate the complete payload before touching the live GUI.
        // A malformed save must not close an active proof draft or leave the
        // renderer disabled.
        const parsed = JSON.parse(str);
        const formatVersion = Array.isArray(parsed) ? 0 : Number(parsed?.version) || 0;
        const data = Array.isArray(parsed) ? parsed : parsed?.data;
        if (!Array.isArray(data))
            throw TR("推理系统存档格式无效");
        const fsArrD = initFormalSystem(this.creative);
        const fsdata = this.deserializeArr(fsArrD.fs, data);
        const skipRendering = gui.skipRendering;
        gui.skipRendering = true;
        try {
            // A loaded save owns the next page store; discard any live
            // assistant only after the replacement payload is known to be
            // valid.
            gui.closeInferenceProofAssistant?.();
            const savedMetarules = gui.formalSystem.fastmetarules;
            gui.formalSystem = fsdata.fs;
            gui.formalSystem.fastmetarules = savedMetarules;
            gui.deductions = fsdata.arrD;
            // Keep the GUI and engine on the same page store. This also
            // migrates old GUI instances that created a standalone store
            // before loading.
            gui.pageStore = gui.formalSystem.inferencePages;
            const active = gui.formalSystem.inferencePages.active;
            gui.formalSystem.propositions = active.propositions;
            if (gui.cmd) {
                gui.cmd.cmdBuffer = active.command.buffer.slice();
                gui.cmd.escClear = active.command.state?.escClear ?? true;
                gui.cmd.lastDeduction = active.command.state?.lastDeduction ?? null;
                gui.cmd.pListMasked = false;
            }
            if (gui.actionInput)
                gui.actionInput.value = active.command.input;
            if (gui.hintText && active.command.state?.hint !== undefined) {
                gui.hintText.innerHTML = active.command.state.hint;
            }
            gui.renderInferencePages?.();
            // Legacy array saves from before the format envelope may have
            // missed the two follow-up Peano unlocks. New saves carry a
            // version marker, so a legitimate current save with only apn3 is
            // left untouched.
            if (formatVersion === 0
                && gui.deductions.includes("apn3")
                && !gui.deductions.includes("apn4")
                && !gui.deductions.includes("apn5")) {
                gui.deductions.push("apn4", "apn5");
            }
            if (fsdata.arrM[0]) {
                gui.metarules = Array.from(new Set(fsdata.arrM.slice(1)));
                this.deserializeMetaMacro(gui, fsdata.arrM[0]);
            }
            gui.updatePropositionList(true);
            gui.updateDeductionList();
            gui.updateMetaRuleList(true);
            // Restore a page-local proof draft only after the loaded rules and
            // proposition lists are available to replay its command history.
            gui.restoreInferenceProofDraft?.(active);
        }
        finally {
            gui.skipRendering = skipRendering;
        }
    }
}
//# sourceMappingURL=savesparser.js.map