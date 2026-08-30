/** Canonical Lean-style syntax for deduction-layer proof-assistant scripts. */

/** Convert one legacy command while loading an old draft/save. */
export function migrateInferenceProofCommand(input: string): string {
    let command = String(input ?? "").trim();
    // Old button/script output used a standalone trailing period.
    command = command.replace(/\s+\.$/, "").trim();

    // Lean uses unicode angle brackets for constructor patterns.  Keep the
    // old ASCII spelling only as an input migration, never in new output.
    command = command.replace(
        /^(obtain\s+)<([^<>]*)>\s*(:=\s*[\s\S]*)$/,
        (_match, prefix: string, pattern: string, suffix: string) => `${prefix}⟨${pattern}⟩ ${suffix}`
    );

    // Legacy form: `have <proposition> <name>`.
    // Canonical Lean form is `have <name> : <proposition>`.
    const legacyHave = /^have\s+([^\s,:=][\s\S]*?)\s+([^\s,:=]+)$/.exec(command);
    if (legacyHave && !/^have\s+[^\s,:=]+\s*(?::|:=)/.test(command)) {
        const proposition = legacyHave[1].trim();
        const name = legacyHave[2].trim();
        if (proposition && name) return `have ${name} : ${proposition}`;
    }
    return command;
}

export function migrateInferenceProofHistory(history: readonly string[] | undefined): string[] {
    return Array.isArray(history)
        ? history.filter((command): command is string => typeof command === "string")
            .map(migrateInferenceProofCommand)
        : [];
}
