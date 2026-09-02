import { migrateLegacyDeclarationSource, migrateLegacyProofHistory, migrateLegacyProofScript, migrateLegacySurfaceExpression } from "./surface-syntax-migration.js";
/**
 * Migrate the syntax-bearing fields of one saved theorem row.  Folder rows
 * deliberately pass through unchanged: their labels and IDs are user data,
 * not type-theory syntax.
 */
function migrateTheoremItem(item) {
    if (!item || item.kind === "folder")
        return item;
    return {
        ...item,
        value: migrateLegacyDeclarationSource(String(item.value ?? ""))
    };
}
/**
 * Save files may contain proof tabs from before the Unicode surface syntax
 * migration.  Clone only the known syntax fields and leave all session
 * bookkeeping (IDs, scope, stale/detached flags, bindings) byte-for-byte.
 */
function migrateProofSessions(value) {
    if (!value || typeof value !== "object")
        return value;
    const envelope = value;
    if (!Array.isArray(envelope.sessions))
        return value;
    return {
        ...envelope,
        sessions: envelope.sessions.map(session => {
            if (!session || typeof session !== "object")
                return session;
            const current = session;
            const migrated = { ...current };
            if (typeof current.target === "string") {
                migrated.target = migrateLegacySurfaceExpression(current.target);
            }
            if (Array.isArray(current.history)) {
                migrated.history = migrateLegacyProofHistory(current.history);
            }
            if (typeof current.script === "string") {
                migrated.script = migrateLegacyProofScript(current.script);
            }
            return migrated;
        })
    };
}
/**
 * Convert a parsed TT save exactly at its load boundary.  Keeping this helper
 * separate makes the one-shot policy explicit and lets non-DOM tests exercise
 * it without constructing the browser GUI.
 */
export function migrateLegacyTTSave(value) {
    const saved = value;
    const rawItems = Array.isArray(saved)
        ? saved.map(item => ({ kind: "theorem", value: item }))
        : (saved && typeof saved === "object" && Array.isArray(saved.items)
            ? saved.items
            : []);
    const items = rawItems.map(item => {
        if (!item || typeof item !== "object") {
            return migrateTheoremItem({ kind: "theorem", value: String(item ?? "") });
        }
        return migrateTheoremItem(item);
    });
    const saveObject = !Array.isArray(saved) && saved && typeof saved === "object"
        ? saved
        : null;
    // Version 3 is the only persisted format that officially carries proof
    // tabs.  The helper's own version-less output is also accepted so a
    // second invocation remains an exact no-op (useful for tests and callers
    // composing load adapters); older versioned saves still discard tabs as
    // they did before the migration was introduced.
    const proofSessions = saveObject
        && (saveObject.version === 3
            || (saveObject.version === undefined
                && Object.prototype.hasOwnProperty.call(saveObject, "proofSessions")))
        ? migrateProofSessions(saveObject.proofSessions)
        : undefined;
    return { items, proofSessions };
}
export class SavesParser {
    serialize(gui) {
        return JSON.stringify({
            version: 3,
            items: gui.serializeTheoremItems(),
            proofSessions: gui.serializeProofSessions()
        });
    }
    deserialize(gui, s) {
        const saved = JSON.parse(s);
        const migrated = migrateLegacyTTSave(saved);
        gui.resetProofAssistantForSaveLoad();
        gui.restoreTheoremItems(migrated.items);
        gui.queueProofSessionsRestore(migrated.proofSessions);
        // gui.updateAfterUnlock();
        // gui.getInhabitatArray()[0]?.onblur({} as any);
    }
}
//# sourceMappingURL=savesparser.js.map