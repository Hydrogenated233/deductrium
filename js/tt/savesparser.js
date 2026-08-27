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
        const items = Array.isArray(saved)
            ? saved.map(value => ({ kind: "theorem", value }))
            : saved?.items;
        const proofSessions = !Array.isArray(saved) && saved?.version === 3
            ? saved.proofSessions
            : undefined;
        gui.resetProofAssistantForSaveLoad();
        gui.restoreTheoremItems(Array.isArray(items) ? items : []);
        gui.queueProofSessionsRestore(proofSessions);
        // gui.updateAfterUnlock();
        // gui.getInhabitatArray()[0]?.onblur({} as any);
    }
}
//# sourceMappingURL=savesparser.js.map