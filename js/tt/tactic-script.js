import { expandTypeTheoryAliasesInSurface } from "./symbol-aliases.js";
export class TTTacticScriptError extends Error {
    lineNumber;
    constructor(lineNumber, message) {
        super(`第 ${lineNumber} 行：${message}`);
        this.lineNumber = lineNumber;
    }
}
/** Worker/process transports wrap Error strings but preserve the block line. */
export function locateTTTacticError(error, blockStartLine) {
    const match = /^(?:\w*Error:\s*)*第 (\d+) 行：([\s\S]*)$/.exec(String(error));
    return match ? {
        lineNumber: blockStartLine + Number(match[1]) - 1,
        message: match[2]
    } : null;
}
/** Parse layout once for both the text editor and the worker command boundary. */
export function parseTTTacticScript(source) {
    const rawLines = source.split(/\r?\n/);
    const lines = [];
    for (let index = 0; index < rawLines.length; index++) {
        const raw = rawLines[index];
        const content = expandTypeTheoryAliasesInSurface(raw.replace(/(^|\s)--.*$/, ""))
            .trim().replace(/\s+\.$/, "").trim();
        if (!content)
            continue;
        const whitespace = raw.match(/^\s*/)[0];
        if (whitespace.includes("\t")) {
            throw new TTTacticScriptError(index + 1, "策略缩进请使用空格，不要使用 Tab");
        }
        lines.push({ content, indent: whitespace.length, lineNumber: index + 1 });
    }
    let cursor = 0;
    let count = 0;
    const sequence = (indent, depth) => {
        const nodes = [];
        while (cursor < lines.length && lines[cursor].indent >= indent) {
            const line = lines[cursor++];
            if (depth > 64 || ++count > 4096) {
                throw new TTTacticScriptError(line.lineNumber, "策略脚本过大或嵌套过深");
            }
            if (line.indent !== indent) {
                throw new TTTacticScriptError(line.lineNumber, "缩进不匹配；子证明需要 by 或 ·");
            }
            let kind = "tactic";
            let command = line.content;
            let inline;
            const have = /^have\s+(.+?)\s*:=\s*by(?:\s+(.*))?$/.exec(command);
            const exact = /^exact\s+by(?:\s+(.*))?$/.exec(command);
            const by = /^by(?:\s+(.*))?$/.exec(command);
            const focus = /^·(?:\s+(.*))?$/.exec(command);
            if (have) {
                kind = "have";
                command = `have ${have[1]}`;
                inline = have[2];
            }
            else if (exact) {
                kind = "exact";
                inline = exact[1];
            }
            else if (focus) {
                kind = "focus";
                inline = focus[1];
            }
            else if (by) {
                kind = "sequence";
                inline = by[1];
            }
            let body = [];
            if (kind !== "tactic") {
                if (inline) {
                    lines.splice(cursor, 0, {
                        content: inline, indent: indent + 2, lineNumber: line.lineNumber
                    });
                }
                if (cursor >= lines.length || lines[cursor].indent <= indent) {
                    throw new TTTacticScriptError(line.lineNumber, "子证明不能为空");
                }
                body = sequence(lines[cursor].indent, depth + 1);
            }
            const lastLine = lines[cursor - 1].lineNumber;
            nodes.push({
                kind, command, body, lineNumber: line.lineNumber,
                source: [
                    line.content,
                    ...rawLines.slice(line.lineNumber, lastLine).map(raw => raw.slice(indent))
                ].join("\n")
            });
        }
        return nodes;
    };
    if (!lines.length)
        return [];
    const nodes = sequence(lines[0].indent, 0);
    if (cursor !== lines.length) {
        throw new TTTacticScriptError(lines[cursor].lineNumber, "缩进不匹配");
    }
    // A top-level `by` is a script wrapper, not an indivisible undo entry.
    if (nodes[0]?.kind === "sequence") {
        return [...nodes[0].body, ...nodes.slice(1)];
    }
    return nodes;
}
//# sourceMappingURL=tactic-script.js.map