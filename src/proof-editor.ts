const PROOF_COMMANDS = new Set([
    "intro", "intros", "destruct", "ex", "case", "exact", "apply", "rw", "rwb", "nth_rw",
    "simpl", "simp", "rfl", "expand", "fnext", "eq", "sup", "qed", "have", "use", "obtain",
    "revert", "assumption", "constructor", "left", "right", "symm", "contradiction", "by_contra",
    "by_cases", "contrapose", "tauto"
]);

function escapeHtml(value: string): string {
    return value.replace(/[&<>"']/g, character => ({
        "&": "&amp;",
        "<": "&lt;",
        ">": "&gt;",
        '"': "&quot;",
        "'": "&#39;"
    }[character] ?? character));
}

function tokenSpan(className: string, value: string): string {
    return `<span class="proof-token-${className}">${escapeHtml(value)}</span>`;
}

export interface ProofEditorBoxMetrics {
    offsetWidth: number;
    clientWidth: number;
    offsetHeight: number;
    clientHeight: number;
    borderHorizontal?: number;
    borderVertical?: number;
}

/** Return the non-overlay scrollbar gutters occupied by a textarea. */
export function computeProofEditorGutters(metrics: ProofEditorBoxMetrics): {
    right: number;
    bottom: number;
} {
    const borderHorizontal = metrics.borderHorizontal ?? 0;
    const borderVertical = metrics.borderVertical ?? 0;
    return {
        right: Math.max(0, metrics.offsetWidth - metrics.clientWidth - borderHorizontal),
        bottom: Math.max(0, metrics.offsetHeight - metrics.clientHeight - borderVertical)
    };
}

/** Lightweight highlighting for the shared proof-command surface syntax. */
export function highlightProofScript(source: string): string {
    const lines = source.split("\n");
    return lines.map(line => {
        let output = "";
        let offset = 0;
        let firstToken = true;
        const tokenPattern = /--.*$|\?\?|[_]|@[A-Za-z_$][\w$]*|\$[A-Za-z0-9_$?]*|[A-Za-z_][\w!?-]*|[()[\]{},.:=|<>~*&+\-/\\▪→≃≡]/gu;
        for (const match of line.matchAll(tokenPattern)) {
            const index = match.index ?? 0;
            output += escapeHtml(line.slice(offset, index));
            const token = match[0];
            if (token.startsWith("--")) {
                output += tokenSpan("comment", line.slice(index));
                offset = line.length;
                break;
            }
            if (firstToken && PROOF_COMMANDS.has(token)) {
                output += tokenSpan("command", token);
            } else if (token === "_" || token === "??" || token.startsWith("$")) {
                output += tokenSpan("hole", token);
            } else if (/^[A-Za-z_@]/u.test(token)) {
                output += tokenSpan("identifier", token);
            } else if (/^[()[\]{},.:=|<>~*&+\-/\\▪→≃≡]$/u.test(token)) {
                output += tokenSpan("punctuation", token);
            } else {
                output += escapeHtml(token);
            }
            if (/\S/u.test(token)) firstToken = false;
            offset = index + token.length;
        }
        output += escapeHtml(line.slice(offset));
        return output;
    }).join("\n");
}

/** Overlay a syntax-highlighted pre over a transparent textarea. */
export class ProofScriptEditor {
    private readonly highlight: HTMLElement | null;
    private readonly resizeObserver: ResizeObserver | null;

    constructor(readonly textarea: HTMLTextAreaElement) {
        const parent = textarea.parentElement;
        if (!parent) {
            this.highlight = null;
            this.resizeObserver = null;
            return;
        }
        parent.classList.add("proof-code-editor");
        const existing = parent.querySelector<HTMLElement>(".proof-code-highlight");
        this.highlight = existing ?? document.createElement("pre");
        if (!existing) {
            this.highlight.className = "proof-code-highlight";
            this.highlight.setAttribute("aria-hidden", "true");
            parent.insertBefore(this.highlight, textarea);
        }
        textarea.classList.add("proof-code-input");
        textarea.addEventListener("input", () => this.refresh());
        textarea.addEventListener("scroll", () => this.syncScroll());
        this.resizeObserver = typeof ResizeObserver === "undefined"
            ? null
            : new ResizeObserver(() => this.syncLayout());
        this.resizeObserver?.observe(textarea);
        this.refresh();
    }

    refresh(): void {
        if (!this.highlight) return;
        this.highlight.innerHTML = highlightProofScript(this.textarea.value) || "\u00a0";
        this.syncScroll();
    }

    private syncScroll(): void {
        if (!this.highlight) return;
        this.syncLayout();
        this.highlight.scrollTop = this.textarea.scrollTop;
        this.highlight.scrollLeft = this.textarea.scrollLeft;
    }

    private syncLayout(): void {
        if (!this.highlight || typeof getComputedStyle !== "function") return;
        const style = getComputedStyle(this.textarea);
        const parsePixels = (value: string) => Number.parseFloat(value) || 0;
        const gutters = computeProofEditorGutters({
            offsetWidth: this.textarea.offsetWidth,
            clientWidth: this.textarea.clientWidth,
            offsetHeight: this.textarea.offsetHeight,
            clientHeight: this.textarea.clientHeight,
            borderHorizontal: parsePixels(style.borderLeftWidth) + parsePixels(style.borderRightWidth),
            borderVertical: parsePixels(style.borderTopWidth) + parsePixels(style.borderBottomWidth)
        });
        this.highlight.style.right = `${gutters.right}px`;
        this.highlight.style.bottom = `${gutters.bottom}px`;
    }
}

/** Return script text through the complete line containing the caret. */
export function scriptThroughCaret(textarea: HTMLTextAreaElement): string {
    const source = textarea.value;
    const caret = Math.max(0, Math.min(source.length, textarea.selectionStart ?? source.length));
    const lineEnd = source.indexOf("\n", caret);
    return source.slice(0, lineEnd < 0 ? source.length : lineEnd);
}
