/** Syntax-only lookup: callers supply names from their current proof scope. */
export function completeProofInput(source, caret, context, explicit = false) {
    const empty = { start: caret, end: caret, items: [] };
    const before = source.slice(0, caret);
    const line = before.slice(before.lastIndexOf("\n") + 1);
    if (line.includes("--") || /["`]/.test(line))
        return empty;
    const alias = /\\([A-Za-z][A-Za-z0-9]*|\*)?$/.exec(line);
    if (alias) {
        const start = caret - alias[0].length;
        if (start > 0 && /[\p{L}\p{N}_\\]/u.test(source[start - 1]))
            return empty;
        const prefix = (alias[1] ?? "").toLowerCase();
        const tail = /^[A-Za-z0-9]*/.exec(source.slice(caret))[0];
        return { start, end: caret + tail.length, items: context.aliases
                .filter(entry => entry.alias.toLowerCase().startsWith(prefix))
                .sort((a, b) => Number(b.alias.toLowerCase() === prefix) - Number(a.alias.toLowerCase() === prefix))
                .map(entry => ({ label: `\\${entry.alias}  ${entry.symbol}`, insert: entry.symbol, kind: "符号" })) };
    }
    const token = /[\p{L}\p{N}_@.$?!'><~&|]+$/u.exec(line);
    if (!token && !explicit && (!line.trim() || !/[\s([]$/.test(line)))
        return empty;
    const prefix = token?.[0] ?? "";
    const start = caret - prefix.length;
    const tail = /^[\p{L}\p{N}_@.$?!'><~&|]*/u.exec(source.slice(caret))[0];
    const preceding = line.slice(0, line.length - prefix.length).trim()
        .replace(/^·\s*/, "").replace(/^by\s+/, "");
    const commandPosition = !preceding || preceding === "by" || preceding === "·"
        || /:=\s*by$/.test(preceding) || preceding === "exact by";
    const command = preceding.split(/\s/)[0];
    if (!commandPosition && ["intro", "intros", "rintro", "qed"].includes(command))
        return empty;
    if (!commandPosition && /^(have|obtain)\b/.test(preceding) && !/[:=]/.test(preceding))
        return empty;
    if (preceding.lastIndexOf(" with") > preceding.lastIndexOf(" generalizing"))
        return empty;
    const localOnly = /\b(at|generalizing)\b/.test(preceding) || command === "revert";
    const values = commandPosition
        ? [[context.commands, "策略"]]
        : [[context.locals, "局部"], [localOnly ? [] : context.constants, "定理"]];
    const seen = new Set();
    const items = [];
    if (["cases", "destruct", "rcases", "induction"].includes(command)
        && /\s/.test(preceding) && !/\bgeneralizing\b/.test(preceding)) {
        for (const keyword of ["generalizing", "with"]) {
            if (keyword.startsWith(prefix))
                items.push({ label: keyword, insert: keyword, kind: "选项" });
        }
    }
    for (const [names, kind] of values) {
        for (const name of names) {
            if (!name.startsWith(prefix) || seen.has(name))
                continue;
            seen.add(name);
            items.push({ label: name, insert: name, kind });
        }
    }
    return { start, end: caret + tail.length, items };
}
let nextPopupId = 0;
/** One controller for command inputs and multiline script editors. */
export function installProofCompletion(input, getContext, multiline = false) {
    if (!input)
        return;
    const popup = document.createElement("div");
    popup.className = "proof-completions";
    popup.id = `proof-completions-${++nextPopupId}`;
    popup.setAttribute("role", "listbox");
    popup.hidden = true;
    document.body.appendChild(popup);
    input.setAttribute("aria-controls", popup.id);
    input.setAttribute("aria-autocomplete", "list");
    input.setAttribute("aria-expanded", "false");
    let result = { start: 0, end: 0, items: [] };
    let selected = 0;
    let composing = false;
    const close = () => {
        popup.hidden = true;
        input.setAttribute("aria-expanded", "false");
        input.removeAttribute("aria-activedescendant");
    };
    const replace = (start, end, text) => {
        input.setRangeText(text, start, end, "end");
        close();
        input.dispatchEvent(new Event("input", { bubbles: true }));
        close();
    };
    const accept = () => {
        const item = result.items[selected];
        if (composing || input.disabled || input.selectionStart !== input.selectionEnd)
            return close();
        const current = completeProofInput(input.value, input.selectionStart ?? 0, getContext(), true);
        if (item && current.start === result.start && current.end === result.end
            && current.items.some(candidate => candidate.insert === item.insert)) {
            replace(current.start, current.end, item.insert);
            return true;
        }
        close();
        return false;
    };
    const position = () => {
        const rect = input.getBoundingClientRect();
        const width = Math.min(360, window.innerWidth - 16);
        popup.style.width = `${width}px`;
        popup.style.left = `${Math.max(8, Math.min(rect.left, window.innerWidth - width - 8))}px`;
        const height = Math.min(240, popup.scrollHeight);
        popup.style.top = `${rect.bottom + height + 8 <= window.innerHeight
            ? rect.bottom + 4 : Math.max(8, rect.top - height - 4)}px`;
    };
    const render = () => {
        popup.replaceChildren();
        // Keep keyboard navigation complete without rendering huge symbol lists.
        const first = Math.max(0, selected - 5);
        result.items.slice(first, first + 10).forEach((item, offset) => {
            const index = first + offset;
            const row = document.createElement("div");
            row.id = `${popup.id}-${index}`;
            row.className = "proof-completion-option";
            row.setAttribute("role", "option");
            row.setAttribute("aria-selected", String(index === selected));
            const label = document.createElement("span");
            label.textContent = item.label;
            const kind = document.createElement("small");
            kind.textContent = item.kind;
            row.append(label, kind);
            row.addEventListener("mousedown", event => {
                event.preventDefault();
                selected = index;
                accept();
            });
            popup.appendChild(row);
        });
        popup.hidden = !result.items.length;
        input.setAttribute("aria-expanded", String(!popup.hidden));
        if (!popup.hidden) {
            input.setAttribute("aria-activedescendant", `${popup.id}-${selected}`);
            position();
        }
    };
    const refresh = (explicit = false) => {
        if (composing || input.disabled || document.activeElement !== input
            || input.selectionStart !== input.selectionEnd)
            return close();
        result = completeProofInput(input.value, input.selectionStart ?? input.value.length, getContext(), explicit);
        selected = 0;
        render();
    };
    input.addEventListener("input", () => refresh());
    input.addEventListener("click", () => refresh());
    input.addEventListener("keyup", event => {
        if (["ArrowLeft", "ArrowRight", "Home", "End"].includes(event.key))
            refresh();
    });
    input.addEventListener("blur", close);
    input.addEventListener("compositionstart", () => { composing = true; close(); });
    input.addEventListener("compositionend", () => { composing = false; refresh(); });
    window.addEventListener("resize", close);
    window.addEventListener("scroll", close, true);
    input.addEventListener("keydown", event => {
        const key = event;
        if (composing || key.isComposing || key.keyCode === 229)
            return;
        const consume = () => { key.preventDefault(); key.stopImmediatePropagation(); };
        if (key.key === "Escape" && !popup.hidden) {
            consume();
            close();
            return;
        }
        if (key.ctrlKey || key.metaKey || key.altKey) {
            if (key.ctrlKey && key.key === " ") {
                consume();
                refresh(true);
            }
            return;
        }
        if (["ArrowDown", "ArrowUp"].includes(key.key) && !popup.hidden) {
            consume();
            selected = (selected + (key.key === "ArrowDown" ? 1 : -1) + result.items.length) % result.items.length;
            render();
            return;
        }
        if ((key.key === "Enter" || key.key === "Tab") && !key.shiftKey) {
            if (popup.hidden && key.key === "Tab")
                refresh();
            if (!popup.hidden && result.items.length) {
                if (accept()) {
                    consume();
                    return;
                }
            }
        }
        if (key.key === "Tab" && multiline) {
            consume();
            const start = input.selectionStart ?? 0;
            const end = input.selectionEnd ?? start;
            const lineStart = input.value.lastIndexOf("\n", start - 1) + 1;
            if (start !== end) {
                const blockEnd = input.value[end - 1] === "\n" ? end - 1 : end;
                const block = input.value.slice(lineStart, blockEnd);
                const replacement = key.shiftKey ? block.replace(/^ {1,2}/gm, "") : block.replace(/^/gm, "  ");
                replace(lineStart, blockEnd, replacement);
                input.setSelectionRange(lineStart, lineStart + replacement.length);
            }
            else if (key.shiftKey) {
                const spaces = /^ {1,2}/.exec(input.value.slice(lineStart))?.[0].length ?? 0;
                if (spaces)
                    replace(lineStart, lineStart + spaces, "");
            }
            else {
                replace(start, end, "  ");
            }
        }
        else if (!["Shift", "Control", "Alt", "Meta"].includes(key.key)) {
            close();
        }
    }, true);
}
//# sourceMappingURL=proof-completion.js.map