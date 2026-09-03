export type OrderedTheoremItem = { kind: "theorem" | "folder" };

export type TheoremInferenceNode = {
    type: string;
    name?: string;
    nodes?: readonly TheoremInferenceNode[];
    checked?: TheoremInferenceNode | null;
    nbeGeneratedMeta?: true;
};

/** Determine whether every legacy inference hole has enough checked metadata. */
export function theoremInferenceComplete(ast: TheoremInferenceNode | null | undefined) {
    const seen = new WeakSet<object>();
    const visit = (
        node: TheoremInferenceNode | null | undefined,
        parent: TheoremInferenceNode | null = null,
        childIndex = -1
    ): boolean => {
        if (!node || seen.has(node)) return true;
        seen.add(node);
        const isPrivateNbeVariable = node.nbeGeneratedMeta === true;
        // NbE may materialize a private metavariable for the implicit equality
        // argument of `refl`.  That particular slot is an implementation
        // detail; private metavariables elsewhere still represent unresolved
        // inference and must keep the declaration in the `infering` state.
        const isReflImplicitArgument = isPrivateNbeVariable
            && parent?.type === "apply"
            && childIndex > 0
            && (parent.nodes?.[0]?.type === "var")
            && (parent.nodes?.[0]?.name === "refl" || parent.nodes?.[0]?.name === "@refl");
        if (node.type === "var" && !isReflImplicitArgument
            && (node.name === "_" || node.name?.startsWith("?"))) {
            if (!node.checked) return false;
            const checkedType = node.checked.type === ":"
                ? node.checked.nodes?.[1]
                : node.checked;
            if (checkedType?.name === "U@") return true;
            if (checkedType?.type === "apply"
                && checkedType.nodes?.[0]?.name === "U") return true;
            return node.checked.type === ":"
                ? visit(node.checked.nodes?.[0], node.checked, 0)
                : false;
        }
        return (node.nodes ?? []).every((child, index) => visit(child, node, index));
    };
    return visit(ast);
}

export type TheoremInferenceStatus = "complete" | "incomplete" | "legacy";

/** Interpret the optional Worker signal while retaining compatibility with older callers. */
export function theoremInferenceStatus(inferenceComplete: boolean | undefined): TheoremInferenceStatus {
    if (inferenceComplete === true) return "complete";
    if (inferenceComplete === false) return "incomplete";
    return "legacy";
}

/**
 * Keep the user's surface declaration for rendering, but inspect the Worker's
 * elaborated definition when deciding whether inference is complete.
 */
export function theoremInferenceTarget<T extends TheoremInferenceNode>(
    surfaceAst: T,
    filledDefinition?: T
) {
    return surfaceAst.type === ":=" && filledDefinition
        ? filledDefinition
        : surfaceAst;
}

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

/** Return the first theorem whose pending check still matters. */
export function findEarliestPendingTheorem<T>(
    theorems: readonly T[],
    isPending: (theorem: T) => boolean,
    isDisabled: (theorem: T) => boolean
) {
    return theorems.find(theorem => isPending(theorem) && !isDisabled(theorem));
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

/** A wall-clock Worker timeout must not rerun the same expensive check on the UI thread. */
export function shouldFallbackToSynchronousTheoremValidation(error: unknown) {
    if (error && typeof error === "object" && (error as any).preventSynchronousFallback) return false;
    const message = error instanceof Error ? error.message : String(error);
    return !message.includes("Type-theory worker timed out")
        && !message.includes("Type-theory process timed out");
}

export function typeTheoryValidationTimedOut(error: unknown) {
    const message = error instanceof Error ? error.message : String(error);
    return (error && typeof error === "object" && (error as any).code === "TT_PROCESS_TIMEOUT")
        || message.includes("timed out")
        || message.includes("验证超时");
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
    private idleWaiters: (() => void)[] = [];

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
        if (this.pendingStartIndex === null) {
            const waiters = this.idleWaiters;
            this.idleWaiters = [];
            for (const resolve of waiters) resolve();
            return null;
        }
        const startIndex = this.pendingStartIndex;
        this.pendingStartIndex = null;
        const run = { id: ++this.nextId, startIndex, cancelled: false };
        this.activeRun = run;
        return { id: run.id, startIndex: run.startIndex };
    }

    /** Wait until the active validation and every coalesced follow-up have committed. */
    waitForIdle(): Promise<void> {
        if (!this.activeRun) return Promise.resolve();
        return new Promise(resolve => this.idleWaiters.push(resolve));
    }

    get hasActiveRun() {
        return this.activeRun !== null;
    }
}
