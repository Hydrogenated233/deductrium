/**
 * DOM-free state for the type-theory proof-assistant tabs.
 *
 * Only the active session is executed by the GUI/Worker adapter. Inactive
 * sessions retain enough source state to be replayed lazily when activated.
 */

export type TTProofSessionId = string;
export type TTProofSessionKind = "theorem" | "manual" | "gate";

export interface TTProofSession {
    readonly id: TTProofSessionId;
    readonly kind: TTProofSessionKind;
    /** Optional user-facing page name; an empty string uses the automatic label. */
    title: string;
    target: string;
    history: string[];
    script: string;
    scopeFolderId: string | null;
    /** False follows the theorem's default folder; true preserves user choice. */
    scopeExplicit: boolean;
    theoremItemId: string | null;
    /**
     * Position fallback for saves whose theorem row ids were regenerated.
     * The stable theoremItemId remains authoritative while it is available.
     */
    targetTheoremIndex: number | null;
    stale: boolean;
    detached: boolean;
}

export interface TTProofSessionInit {
    id?: TTProofSessionId;
    kind: TTProofSessionKind;
    title?: string;
    target: string;
    history?: readonly string[];
    script?: string;
    scopeFolderId?: string | null;
    scopeExplicit?: boolean;
    theoremItemId?: string | null;
    targetTheoremIndex?: number | null;
    stale?: boolean;
    detached?: boolean;
}

export interface TTTheoremProofSessionInit {
    title?: string;
    target: string;
    theoremItemId: string;
    targetTheoremIndex: number;
    scopeFolderId?: string | null;
    scopeExplicit?: boolean;
    history?: readonly string[];
    script?: string;
}

export interface TTUnboundProofSessionInit {
    title?: string;
    target: string;
    scopeFolderId?: string | null;
    scopeExplicit?: boolean;
    history?: readonly string[];
    script?: string;
}

export type TTProofSessionPatch = Partial<Pick<TTProofSession,
    "title"
    | "target"
    | "history"
    | "script"
    | "scopeFolderId"
    | "scopeExplicit"
    | "stale"
    | "detached"
>>;

export interface SerializedTTProofSessions {
    sessions: TTProofSession[];
    activeId: TTProofSessionId | null;
}

function cloneHistory(history?: readonly string[]): string[] {
    return Array.isArray(history)
        ? history.filter((command): command is string => typeof command === "string")
        : [];
}

function normalizeTheoremIndex(index: unknown): number | null {
    return typeof index === "number" && Number.isInteger(index) && index >= 0
        ? index
        : null;
}

function cloneSession(session: TTProofSession): TTProofSession {
    return {
        id: session.id,
        kind: session.kind,
        title: session.title,
        target: session.target,
        history: [...session.history],
        script: session.script,
        scopeFolderId: session.scopeFolderId,
        scopeExplicit: session.scopeExplicit,
        theoremItemId: session.theoremItemId,
        targetTheoremIndex: session.targetTheoremIndex,
        stale: session.stale,
        detached: session.detached
    };
}

/** Ordered, persistent proof drafts. It owns no live proof-engine state. */
export class TTProofSessionStore {
    private readonly sessionsById = new Map<TTProofSessionId, TTProofSession>();
    private orderedIds: TTProofSessionId[] = [];
    private activeSessionId: TTProofSessionId | null = null;
    private nextId = 1;

    constructor(initial: readonly TTProofSessionInit[] = [], activeId?: TTProofSessionId | null) {
        for (const session of initial) this.addInitialSession(session);
        this.activeSessionId = activeId && this.sessionsById.has(activeId)
            ? activeId
            : this.orderedIds[0] ?? null;
    }

    get sessions(): readonly TTProofSession[] {
        return this.orderedIds.map(id => cloneSession(this.sessionsById.get(id)!));
    }

    get activeId(): TTProofSessionId | null {
        return this.activeSessionId;
    }

    get active(): TTProofSession | null {
        const session = this.activeSessionId
            ? this.sessionsById.get(this.activeSessionId)
            : null;
        return session ? cloneSession(session) : null;
    }

    get size(): number {
        return this.orderedIds.length;
    }

    session(id: TTProofSessionId): TTProofSession | undefined {
        const session = this.sessionsById.get(id);
        return session ? cloneSession(session) : undefined;
    }

    sessionAt(index: number): TTProofSession | undefined {
        const id = this.orderedIds[index];
        return id ? this.session(id) : undefined;
    }

    /** Open or activate the sole live session bound to a theorem row. */
    openTheorem(init: TTTheoremProofSessionInit, reuseActiveBlank = false): TTProofSession {
        if (!init.theoremItemId) throw new Error("定理证明会话缺少定理编号");
        const targetTheoremIndex = normalizeTheoremIndex(init.targetTheoremIndex);
        if (targetTheoremIndex === null) throw new Error("定理证明会话缺少定理位置");

        const exact = this.findBoundTheoremSession(init.theoremItemId);
        if (exact) {
            this.moveTheoremSession(exact, targetTheoremIndex);
            this.updateTheoremBinding(exact, init, targetTheoremIndex);
            this.activeSessionId = exact.id;
            return cloneSession(exact);
        }

        const active = reuseActiveBlank ? this.activeMutableSession() : null;
        if (active && this.isBlankSession(active)) {
            this.makeRoomForTheoremSession(targetTheoremIndex);
            this.replaceSession(active.id, {
                id: active.id,
                kind: "theorem",
                title: active.title,
                target: init.target,
                history: init.history,
                script: init.script,
                scopeFolderId: init.scopeFolderId,
                scopeExplicit: init.scopeExplicit,
                theoremItemId: init.theoremItemId,
                targetTheoremIndex
            });
            return this.session(active.id)!;
        }

        this.makeRoomForTheoremSession(targetTheoremIndex);
        return this.create({
            kind: "theorem",
            title: init.title,
            target: init.target,
            history: init.history,
            script: init.script,
            scopeFolderId: init.scopeFolderId,
            scopeExplicit: init.scopeExplicit,
            theoremItemId: init.theoremItemId,
            targetTheoremIndex
        });
    }

    /**
     * Rebind a restored theorem session after theorem row ids were regenerated.
     *
     * This positional fallback is intentionally separate from openTheorem:
     * during live editing, a newly inserted row may occupy another theorem's
     * old index and must never steal that theorem's open proof session.
     */
    rebindTheoremByIndex(init: TTTheoremProofSessionInit): TTProofSession | null {
        if (!init.theoremItemId) throw new Error("定理证明会话缺少定理编号");
        const targetTheoremIndex = normalizeTheoremIndex(init.targetTheoremIndex);
        if (targetTheoremIndex === null) throw new Error("定理证明会话缺少定理位置");
        const session = this.findBoundTheoremSession(init.theoremItemId)
            ?? this.findTheoremSessionAt(targetTheoremIndex);
        if (!session) return null;
        this.moveTheoremSession(session, targetTheoremIndex);
        this.updateTheoremBinding(session, init, targetTheoremIndex);
        return cloneSession(session);
    }

    /** Manual goals always create a distinct tab, even for identical text. */
    openManual(init: TTUnboundProofSessionInit, reuseActiveBlank = false): TTProofSession {
        const active = reuseActiveBlank ? this.activeMutableSession() : null;
        if (active && this.isBlankSession(active)) {
            this.replaceSession(active.id, { ...init, id: active.id, kind: "manual", title: active.title });
            return this.session(active.id)!;
        }
        return this.create({ ...init, kind: "manual" });
    }

    /** Gate goals always create a distinct tab, even for identical text. */
    openGate(init: TTUnboundProofSessionInit, reuseActiveBlank = false): TTProofSession {
        const active = reuseActiveBlank ? this.activeMutableSession() : null;
        if (active && this.isBlankSession(active)) {
            this.replaceSession(active.id, { ...init, id: active.id, kind: "gate", title: active.title });
            return this.session(active.id)!;
        }
        return this.create({ ...init, kind: "gate" });
    }

    /** Create an empty persistent proof page that can receive a target later. */
    openBlank(): TTProofSession {
        return this.create({ kind: "manual", target: "" });
    }

    /** Clear one page without removing its id or position from the page list. */
    reset(id: TTProofSessionId = this.activeSessionId): TTProofSession | null {
        if (!id) return null;
        const session = this.requireSession(id);
        this.replaceSession(id, { id, kind: "manual", title: session.title, target: "" });
        this.activeSessionId = id;
        return this.session(id)!;
    }

    activate(id: TTProofSessionId): TTProofSession {
        const session = this.requireSession(id);
        this.activeSessionId = id;
        return cloneSession(session);
    }

    /** Close a tab; when it was active, prefer its previous adjacent tab. */
    close(id: TTProofSessionId = this.activeSessionId): TTProofSession | null {
        if (!id) return null;
        const session = this.requireSession(id);
        const index = this.orderedIds.indexOf(id);
        const wasActive = id === this.activeSessionId;
        this.orderedIds.splice(index, 1);
        this.sessionsById.delete(id);
        if (wasActive) {
            this.activeSessionId = this.orderedIds[index - 1]
                ?? this.orderedIds[index]
                ?? null;
        }
        return cloneSession(session);
    }

    /** Move a tab before another tab; pass null to append. */
    reorder(id: TTProofSessionId, beforeId: TTProofSessionId | null = null): void {
        this.requireSession(id);
        if (beforeId === id) return;
        if (beforeId !== null) this.requireSession(beforeId);
        const from = this.orderedIds.indexOf(id);
        this.orderedIds.splice(from, 1);
        if (beforeId === null) {
            this.orderedIds.push(id);
            return;
        }
        this.orderedIds.splice(this.orderedIds.indexOf(beforeId), 0, id);
    }

    update(id: TTProofSessionId, patch: TTProofSessionPatch): TTProofSession {
        const session = this.requireSession(id);
        if (typeof patch.title === "string") session.title = patch.title;
        const targetChanged = typeof patch.target === "string" && session.target !== patch.target;
        const scopeChanged = (patch.scopeFolderId === null || typeof patch.scopeFolderId === "string")
            && session.scopeFolderId !== patch.scopeFolderId;
        if (typeof patch.target === "string") session.target = patch.target;
        if (Array.isArray(patch.history)) session.history = cloneHistory(patch.history);
        if (typeof patch.script === "string") session.script = patch.script;
        if (patch.scopeFolderId === null || typeof patch.scopeFolderId === "string") {
            session.scopeFolderId = patch.scopeFolderId;
        }
        if (typeof patch.scopeExplicit === "boolean") session.scopeExplicit = patch.scopeExplicit;
        if (session.kind === "theorem") {
            if (patch.detached === true) this.detachSession(session);
            if (patch.detached === false && session.detached) {
                throw new Error("脱离的证明会话需要重新绑定到定理");
            }
        }
        session.stale ||= targetChanged || scopeChanged;
        if (typeof patch.stale === "boolean") session.stale = patch.stale;
        return cloneSession(session);
    }

    /** Update a moved theorem without activating its proof tab. */
    updateTheoremLocation(
        theoremItemId: string,
        targetTheoremIndex: number,
        scopeFolderId: string | null
    ): TTProofSession | null {
        const session = this.findBoundTheoremSession(theoremItemId);
        if (!session) return null;
        const index = normalizeTheoremIndex(targetTheoremIndex);
        if (index === null) throw new Error("定理证明会话缺少定理位置");
        this.moveTheoremSession(session, index);
        const scopeChanged = !session.scopeExplicit && session.scopeFolderId !== scopeFolderId;
        if (!session.scopeExplicit) session.scopeFolderId = scopeFolderId;
        session.stale ||= scopeChanged;
        return cloneSession(session);
    }

    /** Mark a theorem edit while retaining the user's accepted commands/text. */
    markTheoremTargetChanged(
        theoremItemId: string,
        target: string,
        targetTheoremIndex?: number
    ): TTProofSession | null {
        const session = this.findBoundTheoremSession(theoremItemId);
        if (!session) return null;
        session.target = target;
        if (targetTheoremIndex !== undefined) {
            const index = normalizeTheoremIndex(targetTheoremIndex);
            if (index === null) throw new Error("定理证明会话缺少定理位置");
            this.moveTheoremSession(session, index);
        }
        session.stale = true;
        return cloneSession(session);
    }

    /** Preserve a deleted theorem's draft, but remove it from live binding. */
    detachTheorem(theoremItemId: string): TTProofSession | null {
        const session = this.findBoundTheoremSession(theoremItemId);
        if (!session) return null;
        this.detachSession(session);
        return cloneSession(session);
    }

    serialize(): SerializedTTProofSessions {
        return {
            sessions: this.sessions.map(cloneSession),
            activeId: this.activeSessionId
        };
    }

    static deserialize(serialized?: Partial<SerializedTTProofSessions> | null): TTProofSessionStore {
        if (!serialized || !Array.isArray(serialized.sessions)) return new TTProofSessionStore();
        const sessions: TTProofSessionInit[] = [];
        for (const value of serialized.sessions) {
            if (!value || typeof value !== "object") continue;
            if (value.kind !== "theorem" && value.kind !== "manual" && value.kind !== "gate") continue;
            if (typeof value.id !== "string" || !value.id || typeof value.target !== "string") continue;
            const history = cloneHistory(value.history);
            sessions.push({
                id: value.id,
                kind: value.kind,
                title: typeof value.title === "string" ? value.title : "",
                target: value.target,
                history,
                script: typeof value.script === "string" ? value.script : history.join("\n"),
                scopeFolderId: value.scopeFolderId === null || typeof value.scopeFolderId === "string"
                    ? value.scopeFolderId
                    : null,
                scopeExplicit: value.scopeExplicit === true,
                theoremItemId: value.kind === "theorem" && typeof value.theoremItemId === "string"
                    ? value.theoremItemId
                    : null,
                targetTheoremIndex: value.kind === "theorem"
                    ? normalizeTheoremIndex(value.targetTheoremIndex)
                    : null,
                stale: value.stale === true,
                detached: value.kind === "theorem" && value.detached === true
            });
        }
        return new TTProofSessionStore(
            sessions,
            typeof serialized.activeId === "string" ? serialized.activeId : null
        );
    }

    private create(init: TTProofSessionInit): TTProofSession {
        const id = this.allocateId();
        const session = this.normalizeSession({ ...init, id });
        this.sessionsById.set(id, session);
        this.orderedIds.push(id);
        this.activeSessionId = id;
        return cloneSession(session);
    }

    private replaceSession(id: TTProofSessionId, init: TTProofSessionInit & { id: string }): void {
        this.sessionsById.set(id, this.normalizeSession(init));
    }

    private activeMutableSession(): TTProofSession | null {
        return this.activeSessionId ? this.sessionsById.get(this.activeSessionId) ?? null : null;
    }

    private isBlankSession(session: TTProofSession): boolean {
        return session.kind === "manual"
            && !session.target.trim()
            && session.history.length === 0
            && !session.script.trim();
    }

    private addInitialSession(init: TTProofSessionInit): void {
        const id = init.id ?? this.allocateId();
        if (!id || this.sessionsById.has(id)) throw new Error(`证明会话编号 ${id} 已存在`);
        const session = this.normalizeSession({ ...init, id });
        if (session.kind === "theorem" && !session.detached) {
            const duplicateId = session.theoremItemId && this.findBoundTheoremSession(session.theoremItemId);
            const duplicateIndex = session.targetTheoremIndex !== null
                && this.findTheoremSessionAt(session.targetTheoremIndex);
            if (duplicateId || duplicateIndex) throw new Error("同一定理只能打开一个证明会话");
        }
        this.sessionsById.set(id, session);
        this.orderedIds.push(id);
        this.bumpCounter(id);
    }

    private normalizeSession(init: TTProofSessionInit & { id: string }): TTProofSession {
        if (typeof init.target !== "string") throw new Error("证明会话缺少目标命题");
        const history = cloneHistory(init.history);
        const theorem = init.kind === "theorem";
        const detached = theorem && init.detached === true;
        return {
            id: init.id,
            kind: init.kind,
            title: typeof init.title === "string" ? init.title : "",
            target: init.target,
            history,
            script: typeof init.script === "string" ? init.script : history.join("\n"),
            scopeFolderId: init.scopeFolderId ?? null,
            scopeExplicit: init.scopeExplicit === true,
            theoremItemId: theorem && !detached && typeof init.theoremItemId === "string"
                ? init.theoremItemId
                : null,
            targetTheoremIndex: theorem && !detached
                ? normalizeTheoremIndex(init.targetTheoremIndex)
                : null,
            stale: init.stale === true,
            detached
        };
    }

    private findBoundTheoremSession(theoremItemId: string): TTProofSession | undefined {
        return this.orderedIds
            .map(id => this.sessionsById.get(id)!)
            .find(session => session.kind === "theorem"
                && !session.detached
                && session.theoremItemId === theoremItemId);
    }

    private findTheoremSessionAt(targetTheoremIndex: number): TTProofSession | undefined {
        return this.orderedIds
            .map(id => this.sessionsById.get(id)!)
            .find(session => session.kind === "theorem"
                && !session.detached
                && session.targetTheoremIndex === targetTheoremIndex);
    }

    private updateTheoremBinding(
        session: TTProofSession,
        init: TTTheoremProofSessionInit,
        targetTheoremIndex: number
    ): void {
        const targetChanged = session.target !== init.target;
        const nextScopeExplicit = init.scopeExplicit === undefined
            ? session.scopeExplicit
            : init.scopeExplicit === true;
        const nextScopeFolderId = init.scopeExplicit === undefined && session.scopeExplicit
            ? session.scopeFolderId
            : init.scopeFolderId ?? null;
        const scopeChanged = session.scopeFolderId !== nextScopeFolderId;
        session.target = init.target;
        session.scopeFolderId = nextScopeFolderId;
        session.scopeExplicit = nextScopeExplicit;
        session.theoremItemId = init.theoremItemId;
        session.targetTheoremIndex = targetTheoremIndex;
        session.detached = false;
        session.stale ||= targetChanged || scopeChanged;
    }

    private makeRoomForTheoremSession(targetTheoremIndex: number): void {
        if (!this.findTheoremSessionAt(targetTheoremIndex)) return;
        for (const session of this.boundTheoremSessions()) {
            if (session.targetTheoremIndex !== null
                && session.targetTheoremIndex >= targetTheoremIndex) {
                session.targetTheoremIndex++;
            }
        }
    }

    private moveTheoremSession(session: TTProofSession, targetTheoremIndex: number): void {
        const previous = session.targetTheoremIndex;
        if (previous === targetTheoremIndex) return;
        if (previous === null) {
            this.makeRoomForTheoremSession(targetTheoremIndex);
            session.targetTheoremIndex = targetTheoremIndex;
            return;
        }
        for (const other of this.boundTheoremSessions()) {
            if (other.id === session.id || other.targetTheoremIndex === null) continue;
            if (previous < targetTheoremIndex
                && other.targetTheoremIndex > previous
                && other.targetTheoremIndex <= targetTheoremIndex) {
                other.targetTheoremIndex--;
            } else if (previous > targetTheoremIndex
                && other.targetTheoremIndex >= targetTheoremIndex
                && other.targetTheoremIndex < previous) {
                other.targetTheoremIndex++;
            }
        }
        session.targetTheoremIndex = targetTheoremIndex;
    }

    private boundTheoremSessions(): TTProofSession[] {
        return this.orderedIds
            .map(id => this.sessionsById.get(id)!)
            .filter(session => session.kind === "theorem" && !session.detached);
    }

    private detachSession(session: TTProofSession): void {
        session.detached = true;
        session.theoremItemId = null;
        session.targetTheoremIndex = null;
    }

    private requireSession(id: TTProofSessionId): TTProofSession {
        const session = this.sessionsById.get(id);
        if (!session) throw new Error(`证明会话 ${id} 不存在`);
        return session;
    }

    private allocateId(): TTProofSessionId {
        let id: TTProofSessionId;
        do id = `proof-session-${this.nextId++}`; while (this.sessionsById.has(id));
        return id;
    }

    private bumpCounter(id: TTProofSessionId): void {
        const match = /^proof-session-(\d+)$/.exec(id);
        if (match) this.nextId = Math.max(this.nextId, Number(match[1]) + 1);
    }
}
