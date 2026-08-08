/**
 * Return whether a rendered theorem identifier is known to the current UI
 * context.  The renderer has several name sets (system constants, macros and
 * user definitions); keeping this predicate independent makes it possible to
 * test the classification without constructing a DOM.
 */
export function isKnownTheoremIdentifier(name, ...sets) {
    const normalized = name.replace(/'+$/g, "");
    return sets.some(set => !!set?.has(normalized));
}
/** Convert an item-list position (which includes folders) to a theorem-input index. */
export function theoremInputIndexBeforeItem(items, itemIndex) {
    const end = Math.max(0, Math.min(itemIndex, items.length));
    let theoremIndex = 0;
    for (let i = 0; i < end; i++) {
        if (items[i].kind === "theorem")
            theoremIndex++;
    }
    return theoremIndex;
}
/**
 * An async validation result may only be committed if its input is still at
 * the position and theorem row that produced the request.  Row objects remain
 * connected when a preceding row is inserted, so checking connectivity alone
 * is insufficient.
 */
export function theoremValidationPositionMatches(inputs, input, expectedIndex, expectedItemId, getItemId) {
    return inputs.indexOf(input) === expectedIndex && getItemId(input) === expectedItemId;
}
/** A cached #t preview is stale when its target or either context revision changed. */
export function theoremPreviewNeedsRefresh(target, previousTarget, definitionRevision, previousDefinitionRevision, structureRevision, previousStructureRevision) {
    return target !== previousTarget
        || definitionRevision !== previousDefinitionRevision
        || structureRevision !== previousStructureRevision;
}
/** A click-through with no edit can reuse its already-rendered validation result. */
export function canReuseTheoremResultOnBlur(state) {
    return !state.programmatic
        && state.canReuseRenderedResult
        && typeof state.originalValue === "string"
        && state.originalValue === state.currentValue
        && !state.validationInvalidated
        && !state.updateDefinitions;
}
/**
 * Coalesces overlapping suffix validations. A newer request invalidates the
 * active run, but waits for its in-flight worker call to settle before the
 * latest requested suffix starts. This keeps the persistent worker session
 * from receiving two interleaved validation chains.
 */
export class TheoremValidationCoordinator {
    nextId = 0;
    activeRun = null;
    pendingStartIndex = null;
    request(startIndex) {
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
    isCurrent(runId) {
        return this.activeRun?.id === runId && !this.activeRun.cancelled;
    }
    /** Mark a completed (or cancelled) run and promote the newest queued run. */
    complete(runId) {
        if (!this.activeRun || this.activeRun.id !== runId)
            return null;
        this.activeRun = null;
        if (this.pendingStartIndex === null)
            return null;
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
//# sourceMappingURL=theorem-validation.js.map