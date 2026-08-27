import { TR } from "../lang.js";
import { AssertionSystem } from "./assertion.js";
import { AST, ASTMgr } from "./astmgr.js";
import { FormalSystem } from "./formalsystem.js";
const astmgr = new ASTMgr;
const assert = new AssertionSystem;
type PropWithTruth = [truth: boolean, idx: number];
export class Proof {
    fs: FormalSystem;
    constructor(fs: FormalSystem) {
        this.fs = fs;
    }
    assertTautology(ast: AST) {
        assert.checkGrammer(ast, "p");
        const varTable = assert.getReplVarsType(ast, {}, false);
        if (Object.values(varTable).includes(true)) throw TR("无法对非命题逻辑符号进行真值指派");
        const vars = Object.keys(varTable);
        // The old proof generator uses 32-bit shifts. Reject inputs beyond the
        // representable exhaustive-search range instead of silently accepting
        // an under-enumerated formula when the shift overflows.
        if (vars.length > 30) throw TR("命题变量过多，无法进行重言式测试");
        const hypEnums = 1n << BigInt(vars.length);
        for (let i = 0n; i < hypEnums; i++) {
            if (this.enumTruth(ast, vars, i)) continue;
            throw TR("条件重言式测试失败：真值指派") + vars.map((v, idx) => (v + TR(`为`) + (((i >> BigInt(idx)) & 1n) ? TR("真") : TR("假")))).join(TR("、")) + TR("时命题为假");
        }
    }
    private enumTruth(ast: AST, vars: string[], hyps: bigint): boolean {
        if (ast.type === "replvar") {
            const idx = vars.indexOf(ast.name);
            return idx >= 0 && ((hyps >> BigInt(idx)) & 1n) === 1n;
        }
        if (ast.type === "sym") {
            switch (ast.name) {
                case "~": return !this.enumTruth(ast.nodes[0], vars, hyps);
                case ">": return !this.enumTruth(ast.nodes[0], vars, hyps) || this.enumTruth(ast.nodes[1], vars, hyps);
                case "<>": return this.enumTruth(ast.nodes[0], vars, hyps) === this.enumTruth(ast.nodes[1], vars, hyps);
                case "|": return this.enumTruth(ast.nodes[0], vars, hyps) || this.enumTruth(ast.nodes[1], vars, hyps);
                case "&": return this.enumTruth(ast.nodes[0], vars, hyps) && this.enumTruth(ast.nodes[1], vars, hyps);
            }
        }
        throw TR("无法对非命题逻辑符号进行真值指派");
    }
    prove(ast: AST) {
        const varTable = assert.getReplVarsType(ast, {}, false);
        if (Object.values(varTable).includes(true)) throw TR("无法对非命题逻辑符号进行真值指派");
        const vars = Object.keys(varTable);
        const hypEnums = 1 << vars.length;
        const proofEnumsTable: number[] = [];
        const fastrules = this.fs.fastmetarules;
        this.fs.fastmetarules = "cvuqe><:#zZQR";
        try {
            for (let i = 0; i < hypEnums; i++) {
                const [t, p] = this.enumProve(ast, vars, i);
                if (!t) {
                    this.fs.fastmetarules = fastrules;
                    throw TR("条件重言式测试失败：真值指派") + vars.map((v, idx) => (v + TR(`为`) + (((1 << idx) & i) ? TR("真") : TR("假")))).join(TR("、")) + TR("时命题为假");
                }
                proofEnumsTable.push(p);
            }
            for (let idx = 0; idx < vars.length; idx++) {
                for (let i = 0; i < hypEnums >> (idx + 1); i++) {
                    const prefix = "".padEnd(vars.length - idx - 1, "c");
                    const p1 = proofEnumsTable[i];
                    const p2 = proofEnumsTable[i + (hypEnums >> (idx + 1))];
                    const p3 = this.fs.deduct({
                        deductionIdx: prefix + ".m2",
                        conditionIdxs: [p2, p1], replaceValues: [],
                    })
                    proofEnumsTable[i] = p3;
                }
            }
        } catch (e) {
            this.fs.fastmetarules = fastrules;
            throw e;
        }
        this.fs.fastmetarules = fastrules;
    }
    enumProve(ast: AST, vars: string[], hyps: number): PropWithTruth {
        const varsLen = vars.length;
        const prefix = "".padEnd(varsLen, "c");
        if (ast.type === "replvar") {
            return this.cca1(vars, vars.indexOf(ast.name), hyps);
        }
        if (ast.type === "sym") {
            if (ast.name === "~") {
                const [ta, pa] = this.enumProve(ast.nodes[0], vars, hyps);
                if (!ta) return [true, pa];
                return [false, this.fs.deduct({ deductionIdx: prefix + "<.ni", conditionIdxs: [pa], replaceValues: [] })];
            }
            if (ast.name === ">") {
                const prevLen = this.fs.propositions.length;
                const [tb, pb] = this.enumProve(ast.nodes[1], vars, hyps);
                // . > T : T
                if (tb) {
                    return [true, this.fs.deduct({ deductionIdx: prefix + "<a1", conditionIdxs: [pb], replaceValues: [ast.nodes[0]] })];
                }
                const [ta, pa] = this.enumProve(ast.nodes[0], vars, hyps);
                // T > F : F
                if (ta) {
                    return [false, this.fs.deduct({ deductionIdx: prefix + ".>TF", conditionIdxs: [pa, pb], replaceValues: [] })];
                }
                // F > U : T
                return [true, this.fs.deduct({ deductionIdx: prefix + ".>FU", conditionIdxs: [pa], replaceValues: [ast.nodes[1]] })];
            }
            if (ast.name === "<>") {
                const [ta, pa] = this.enumProve(ast.nodes[0], vars, hyps);
                const [tb, pb] = this.enumProve(ast.nodes[1], vars, hyps);
                const dname = (ta ? "T" : "F") + (tb ? "T" : "F");
                return [ta === tb, this.fs.deduct({ deductionIdx: prefix + ".<>" + dname, conditionIdxs: [pa, pb], replaceValues: [] })];
            }
            if (ast.name === "|") {
                const [ta, pa] = this.enumProve(ast.nodes[0], vars, hyps);
                const [tb, pb] = this.enumProve(ast.nodes[1], vars, hyps);
                const dname = ta ? "1" : tb ? "2" : "n";
                const conditionIdxs = ta ? [pa] : tb ? [pb] : [pa, pb];
                const replaceValues = ta ? [ast.nodes[1]] : tb ? [ast.nodes[0]] : [];
                return [ta || tb, this.fs.deduct({ deductionIdx: prefix + ".|" + dname, conditionIdxs, replaceValues })];
            }
            if (ast.name === "&") {
                const [ta, pa] = this.enumProve(ast.nodes[0], vars, hyps);
                const [tb, pb] = this.enumProve(ast.nodes[1], vars, hyps);
                const dname = !ta ? "n1" : !tb ? "n2" : "";
                const conditionIdxs = !ta ? [pa] : !tb ? [pb] : [pa, pb];
                const replaceValues = !ta ? [ast.nodes[1]] : !tb ? [ast.nodes[0]] : [];
                return [ta && tb, this.fs.deduct({ deductionIdx: prefix + ".&" + dname, conditionIdxs, replaceValues })];
            }
        }
        throw TR("无法对非命题逻辑符号进行真值指派");
    }
    cca1(vars: string[], id: number, hyps: number): PropWithTruth {
        const truth = !!((hyps >> id) & 1);
        const len = vars.length;
        const prefix = "".padEnd(id, "c");
        const replaceValues = vars.map((v, idx) => (hyps >> idx) & 1 ? { type: "replvar", name: v } : {
            type: "sym", name: "~", nodes: [{ type: "replvar", name: v }]
        });
        const gen = (l: number) => {
            if (l < 3) throw new Error("cannot reached: proof rule arity is smaller than 3");
            if(l===3) return ":ca1,.cs";
            return ":c"+gen(l-1)+",.cs";
            // if (this.fs.deductions[name]) return name;
            // const p = this.fs.propositions;
            // this.fs.propositions = [];
            // try {
            //     this.fs.addHypothese({ type: "replvar", name: "$0" });
            //     for (let i = 1; i < l; i++) {
            //         this.fs.deduct({
            //             deductionIdx: "<a1", conditionIdxs: [i - 1],
            //             replaceValues: [{ type: "replvar", name: "$" + i }]
            //         });
            //     }
            //     this.fs.addMacro(name, "元规则生成*");
            //     this.fs.propositions = p;
            //     return name;
            // } catch (e) {
            //     this.fs.propositions = p;
            //     throw e;
            // }
        }
        // a>b> c>c
        if (id === len - 1) {
            return [truth, this.fs.deduct({ deductionIdx: prefix + ".i", conditionIdxs: [], replaceValues })];
        }
        // a> b>c>b
        if (id === len - 2) {
            return [truth, this.fs.deduct({ deductionIdx: prefix + "a1", conditionIdxs: [], replaceValues })];
        }
        return [truth, this.fs.deduct({
            deductionIdx: prefix + gen(len - id), conditionIdxs: [], replaceValues
        })];
    }
}

