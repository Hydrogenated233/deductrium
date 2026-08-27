/**
 * Page-local state for the deduction layer.
 *
 * The model deliberately does not know about the formal-system engine or the
 * DOM.  Proposition validation, rendering, persistence and command parsing
 * are adapters around this store.  Keeping those concerns out of the model
 * makes page switching/reordering a pure state operation and preserves the
 * active page by stable id.
 */

export type InferencePageId = string;

/** State that is paused while the user switches to another inference page. */
export interface InferenceCommandSnapshot {
    /** Text currently in the command input. */
    input: string;
    /** Commands already entered but not committed by the command executor. */
    buffer: unknown[];
    /** Parser/command-step state owned by the command adapter. */
    state?: unknown;
}

export interface InferencePage<TProposition = unknown> {
    readonly id: InferencePageId;
    name: string;
    /** Proposition numbers are the array indexes and are page-local. */
    propositions: TProposition[];
    command: InferenceCommandSnapshot;
}

export interface InferencePageInit<TProposition = unknown> {
    id?: InferencePageId;
    name: string;
    propositions?: TProposition[];
    command?: Partial<InferenceCommandSnapshot>;
}

export interface SerializedInferencePage<TProposition = unknown> {
    id: InferencePageId;
    name: string;
    propositions: TProposition[];
    command: InferenceCommandSnapshot;
}

export interface SerializedInferencePages<TProposition = unknown> {
    pages: SerializedInferencePage<TProposition>[];
    activeId: InferencePageId;
}

const PAGE_NAME_RE = /^[\p{L}\p{N}_-]+$/u;

function cloneCommand(command?: Partial<InferenceCommandSnapshot>): InferenceCommandSnapshot {
    return {
        input: command?.input ?? "",
        buffer: [...(command?.buffer ?? [])],
        state: command?.state
    };
}

function clonePropositions<T>(propositions?: T[]): T[] {
    return [...(propositions ?? [])];
}

/**
 * Mutable, UI-independent inference page collection.
 *
 * A page id is the identity used by drag/drop and persistence.  Names are the
 * user-facing command key and are required to be unique.  The store always
 * contains at least one page; the default legacy migration target is `主表`.
 */
export class InferencePageStore<TProposition = unknown> {
    private readonly pagesById = new Map<InferencePageId, InferencePage<TProposition>>();
    private orderedIds: InferencePageId[] = [];
    private nextId = 1;
    private activePageId: InferencePageId;

    constructor(initial?: InferencePageInit<TProposition>[], activeId?: InferencePageId) {
        const source = initial?.length ? initial : [{ name: "主表" }];
        for (const page of source) this.addInitialPage(page);
        this.activePageId = activeId && this.pagesById.has(activeId)
            ? activeId
            : this.orderedIds[0];
    }

    get pages(): readonly InferencePage<TProposition>[] {
        return this.orderedIds.map(id => this.pagesById.get(id)!);
    }

    get activeId(): InferencePageId {
        return this.activePageId;
    }

    get active(): InferencePage<TProposition> {
        return this.pagesById.get(this.activePageId)!;
    }

    get size(): number {
        return this.orderedIds.length;
    }

    page(idOrName: InferencePageId | string): InferencePage<TProposition> | undefined {
        return this.pagesById.get(idOrName) ?? this.pages.find(page => page.name === idOrName);
    }

    pageAt(index: number): InferencePage<TProposition> | undefined {
        const id = this.orderedIds[index];
        return id ? this.pagesById.get(id) : undefined;
    }

    /** Create a page at the end.  The active page is intentionally unchanged. */
    create(name: string, init: Omit<InferencePageInit<TProposition>, "id" | "name"> = {}): InferencePage<TProposition> {
        this.assertPageName(name);
        if (this.pages.some(page => page.name === name || page.id === name)) throw new Error(`推理表 ${name} 已存在`);
        const page: InferencePage<TProposition> = {
            id: this.allocateId(),
            name,
            propositions: clonePropositions(init.propositions),
            command: cloneCommand(init.command)
        };
        this.pagesById.set(page.id, page);
        this.orderedIds.push(page.id);
        return page;
    }

    /** Switch active page by its stable id or user-facing name. */
    activate(idOrName: InferencePageId | string): InferencePage<TProposition> {
        const page = this.requirePage(idOrName);
        this.activePageId = page.id;
        return page;
    }

    /**
     * Delete by stable id or name.  The previous page wins when deleting the
     * active page; if it was the first page, the next page is selected.
     */
    delete(idOrName: InferencePageId | string): InferencePage<TProposition> {
        if (this.size === 1) throw new Error("至少需要保留一个推理表");
        const page = this.requirePage(idOrName);
        const index = this.orderedIds.indexOf(page.id);
        const wasActive = page.id === this.activePageId;
        this.orderedIds.splice(index, 1);
        this.pagesById.delete(page.id);
        if (wasActive) {
            const replacement = this.orderedIds[Math.max(0, index - 1)] ?? this.orderedIds[0];
            this.activePageId = replacement;
        }
        return page;
    }

    /** Move a page before `beforeId`; pass null to append at the end. */
    reorder(idOrName: InferencePageId | string, beforeIdOrName: InferencePageId | string | null = null): void {
        const page = this.requirePage(idOrName);
        if (beforeIdOrName !== null && beforeIdOrName !== "" && this.requirePage(beforeIdOrName).id === page.id) {
            return;
        }
        const from = this.orderedIds.indexOf(page.id);
        this.orderedIds.splice(from, 1);
        if (beforeIdOrName === null || beforeIdOrName === "") {
            this.orderedIds.push(page.id);
            return;
        }
        const before = this.requirePage(beforeIdOrName);
        const destination = this.orderedIds.indexOf(before.id);
        this.orderedIds.splice(destination, 0, page.id);
    }

    setPropositions(propositions: TProposition[], idOrName: InferencePageId | string = this.activePageId): void {
        this.requirePage(idOrName).propositions = clonePropositions(propositions);
    }

    appendProposition(proposition: TProposition, idOrName: InferencePageId | string = this.activePageId): number {
        const page = this.requirePage(idOrName);
        page.propositions.push(proposition);
        return page.propositions.length - 1;
    }

    clearPropositions(idOrName: InferencePageId | string = this.activePageId): void {
        this.requirePage(idOrName).propositions = [];
    }

    setCommandSnapshot(snapshot: Partial<InferenceCommandSnapshot>, idOrName: InferencePageId | string = this.activePageId): void {
        const page = this.requirePage(idOrName);
        page.command = cloneCommand({ ...page.command, ...snapshot });
    }

    serialize(): SerializedInferencePages<TProposition> {
        return {
            activeId: this.activePageId,
            pages: this.pages.map(page => ({
                id: page.id,
                name: page.name,
                propositions: clonePropositions(page.propositions),
                command: cloneCommand(page.command)
            }))
        };
    }

    static deserialize<TProposition = unknown>(serialized: SerializedInferencePages<TProposition>): InferencePageStore<TProposition> {
        if (!serialized || !Array.isArray(serialized.pages) || !serialized.pages.length) {
            return new InferencePageStore<TProposition>();
        }
        return new InferencePageStore<TProposition>(serialized.pages, serialized.activeId);
    }

    private addInitialPage(init: InferencePageInit<TProposition>): void {
        this.assertPageName(init.name);
        if (this.pages.some(page => page.name === init.name || page.id === init.name)) throw new Error(`推理表 ${init.name} 已存在`);
        const id = init.id ?? this.allocateId();
        if (this.pagesById.has(id)) throw new Error(`推理表编号 ${id} 已存在`);
        if (this.pages.some(page => page.name === id)) throw new Error(`推理表编号 ${id} 已存在`);
        const page: InferencePage<TProposition> = {
            id,
            name: init.name,
            propositions: clonePropositions(init.propositions),
            command: cloneCommand(init.command)
        };
        this.pagesById.set(id, page);
        this.orderedIds.push(id);
        this.bumpCounter(id);
    }

    private allocateId(): InferencePageId {
        let id: InferencePageId;
        do id = `page-${this.nextId++}`; while (this.pagesById.has(id));
        return id;
    }

    private bumpCounter(id: InferencePageId): void {
        const match = /^page-(\d+)$/.exec(id);
        if (match) this.nextId = Math.max(this.nextId, Number(match[1]) + 1);
    }

    private assertPageName(name: string): void {
        if (typeof name !== "string" || !PAGE_NAME_RE.test(name)) {
            throw new Error("推理表名称必须是非空单词，只能包含中文、字母、数字、_ 或 -");
        }
    }

    private requirePage(idOrName: InferencePageId | string): InferencePage<TProposition> {
        const page = this.page(idOrName);
        if (!page) throw new Error(`推理表 ${idOrName} 不存在`);
        return page;
    }
}
