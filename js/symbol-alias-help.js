import { INFERENCE_SYMBOL_ALIASES } from "./fs/symbol-aliases.js";
import { TYPE_THEORY_SYMBOL_ALIASES } from "./tt/symbol-aliases.js";
export const SYMBOL_ALIAS_HELP_GROUPS = [
    { title: "推理层", aliases: INFERENCE_SYMBOL_ALIASES },
    { title: "类型层", aliases: TYPE_THEORY_SYMBOL_ALIASES }
];
export function groupSymbolAliases(aliases) {
    const groups = new Map();
    for (const { alias, symbol } of aliases) {
        if (!groups.has(symbol))
            groups.set(symbol, []);
        groups.get(symbol).push(`\\${alias}`);
    }
    return groups;
}
/** Render the complete input tables from the same data used by both editors. */
export function renderSymbolAliases(root) {
    if (!root)
        return;
    root.replaceChildren();
    root.classList.add("symbol-alias-groups");
    for (const { title, aliases } of SYMBOL_ALIAS_HELP_GROUPS) {
        const section = document.createElement("section");
        section.className = "symbol-alias-group";
        const table = document.createElement("table");
        table.className = "symbol-alias-table";
        const caption = table.createCaption();
        caption.textContent = title;
        const head = table.createTHead().insertRow();
        for (const text of ["输入别名", "符号"]) {
            const cell = document.createElement("th");
            cell.scope = "col";
            cell.textContent = text;
            head.appendChild(cell);
        }
        const body = table.createTBody();
        for (const [symbol, spellings] of groupSymbolAliases(aliases)) {
            const row = body.insertRow();
            const input = row.insertCell();
            const list = document.createElement("div");
            list.className = "symbol-alias-spellings";
            for (const spelling of spellings) {
                const code = document.createElement("code");
                code.textContent = spelling;
                list.appendChild(code);
            }
            input.appendChild(list);
            row.insertCell().textContent = symbol;
        }
        const wrapper = document.createElement("div");
        wrapper.className = "symbol-alias-table-wrap";
        wrapper.appendChild(table);
        section.appendChild(wrapper);
        root.appendChild(section);
    }
}
//# sourceMappingURL=symbol-alias-help.js.map