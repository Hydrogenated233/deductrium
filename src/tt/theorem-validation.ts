export type OrderedTheoremItem = { kind: "theorem" | "folder" };

/**
 * Return whether a rendered theorem identifier is known to the current UI
 * context.  The renderer has several name sets (system constants, macros and
 * user definitions); keeping this predicate independent makes it possible to
 * test the classification without constructing a DOM.
 */
export function isKnownTheoremIdentifier(name: string, ...sets: readonly (ReadonlySet<string> | null | undefined)[]) {
    const normalized = name.replace(/'+$/g, "");
    return sets.some(set => !!set?.has(normalized));
}

/** Convert an item-list position (which includes folders) to a theorem-input index. */
export function theoremInputIndexBeforeItem(items: readonly OrderedTheoremItem[], itemIndex: number) {
    const end = Math.max(0, Math.min(itemIndex, items.length));
    let theoremIndex = 0;
    for (let i = 0; i < end; i++) {
        if (items[i].kind === "theorem") theoremIndex++;
    }
    return theoremIndex;
}

/**
 * An async validation result may only be committed if its input is still at
 * the position and theorem row that produced the request.  Row objects remain
 * connected when a preceding row is inserted, so checking connectivity alone
 * is insufficient.
 */
export function theoremValidationPositionMatches<T>(
    inputs: readonly T[],
    input: T,
    expectedIndex: number,
    expectedItemId: string | null,
    getItemId: (input: T) => string | null
) {
    return inputs.indexOf(input) === expectedIndex && getItemId(input) === expectedItemId;
}

/** A cached #t preview is stale when its target or either context revision changed. */
export function theoremPreviewNeedsRefresh(
    target: string,
    previousTarget: string,
    definitionRevision: number,
    previousDefinitionRevision: number,
    structureRevision: number,
    previousStructureRevision: number
) {
    return target !== previousTarget
        || definitionRevision !== previousDefinitionRevision
        || structureRevision !== previousStructureRevision;
}

export type TheoremBlurState = {
    programmatic: boolean;
    canReuseRenderedResult: boolean;
    originalValue?: string;
    currentValue: string;
    validationInvalidated: boolean;
    updateDefinitions: boolean;
};

/** A click-through with no edit can reuse its already-rendered validation result. */
export function canReuseTheoremResultOnBlur(state: TheoremBlurState) {
    return !state.programmatic
        && state.canReuseRenderedResult
        && typeof state.originalValue === "string"
        && state.originalValue === state.currentValue
        && !state.validationInvalidated
        && !state.updateDefinitions;
}

export type TheoremValidationRun = {
    id: number;
    startIndex: number;
};

/**
 * Coalesces overlapping suffix validations. A newer request invalidates the
 * active run, but waits for its in-flight worker call to settle before the
 * latest requested suffix starts. This keeps the persistent worker session
 * from receiving two interleaved validation chains.
 */
export class TheoremValidationCoordinator {
    private nextId = 0;
    private activeRun: (TheoremValidationRun & { cancelled: boolean }) | null = null;
    private pendingStartIndex: number | null = null;

    request(startIndex: number): TheoremValidationRun | null {
        const start = Math.max(0, Math.floor(startIndex));
        if (this.activeRun) {
            this.activeRun.cancelled = true;
            this.pendingStartIndex = this.pendingStartIndex === null
                ? start
                : Math.min(this.pendingStartIndex, start);
            return null;
        }
        const run = { id: ++this.nextId, startIndex: start, cancelled: false };
        this.activeRun = run;
        return { id: run.id, startIndex: run.startIndex };
    }

    isCurrent(runId: number) {
        return this.activeRun?.id === runId && !this.activeRun.cancelled;
    }

    /** Mark a completed (or cancelled) run and promote the newest queued run. */
    complete(runId: number): TheoremValidationRun | null {
        if (!this.activeRun || this.activeRun.id !== runId) return null;
        this.activeRun = null;
        if (this.pendingStartIndex === null) return null;
        const startIndex = this.pendingStartIndex;
        this.pendingStartIndex = null;
        const run = { id: ++this.nextId, startIndex, cancelled: false };
        this.activeRun = run;
        return { id: run.id, startIndex: run.startIndex };
    }

    get hasActiveRun() {
        return this.activeRun !== null;
    }
}
