export class SavesParser {
    serialize(gui) {
        return JSON.stringify({ version: 2, items: gui.serializeTheoremItems() });
    }
    deserialize(gui, s) {
        const saved = JSON.parse(s);
        const items = Array.isArray(saved)
            ? saved.map(value => ({ kind: "theorem", value }))
            : saved?.items;
        gui.restoreTheoremItems(Array.isArray(items) ? items : []);
        // gui.updateAfterUnlock();
        // gui.getInhabitatArray()[0]?.onblur({} as any);
    }
}
//# sourceMappingURL=savesparser.js.map