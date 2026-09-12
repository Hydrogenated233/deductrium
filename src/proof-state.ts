export type ProofStateHypothesis = {
    name: string;
    content: () => Node;
    isType?: boolean;
};

export type ProofStateGoal = {
    id: string;
    name?: string;
    hypotheses: ProofStateHypothesis[];
    target: () => Node;
};

export type ProofStateSettings = {
    targetFirst: boolean;
    hideTypeAssumptions: boolean;
    hideGoalNames: boolean;
    emphasizeFirst: boolean;
};

export type RenderProofStateOptions = {
    goals: ProofStateGoal[];
    expected?: () => Node;
    error?: HTMLElement;
    completedText?: string;
    scope?: string;
    /** Isolate goal folds between proofs that share the same settings scope. */
    contextKey?: string;
    settings?: Partial<ProofStateSettings>;
};

const defaultSettings: ProofStateSettings = {
    targetFirst: false,
    hideTypeAssumptions: false,
    hideGoalNames: false,
    emphasizeFirst: true
};

type ProofStateHostState = {
    scope: string;
    contextKey: string;
    rootOpen: boolean;
    settingsOpen: boolean;
    expectedOpen: boolean;
    messagesOpen: boolean;
    goalsOpen: Map<string, boolean>;
    settings: ProofStateSettings;
    lastOptions: RenderProofStateOptions;
    error?: HTMLElement;
    errorObserver?: MutationObserver;
};

const hostStates = new WeakMap<HTMLElement, ProofStateHostState>();
const hostErrors = new WeakMap<HTMLElement, HTMLElement>();
const settingsByScope = new Map<string, ProofStateSettings>();

function setOpen(element: HTMLDetailsElement, open: boolean) {
    element.open = open;
    if (open) element.setAttribute("open", "");
    else element.removeAttribute("open");
}

function readPreviousState(host: HTMLElement, state: ProofStateHostState) {
    const root = host.querySelector<HTMLDetailsElement>(".proof-state-root");
    if (root) {
        state.rootOpen = root.open;
        state.goalsOpen = new Map(
            Array.from(root.querySelectorAll<HTMLDetailsElement>(".proof-goal"))
                .map(goal => [goal.getAttribute("data-proof-goal-id"), goal.open] as const)
                .filter((entry): entry is readonly [string, boolean] => !!entry[0])
        );
    }
    const settings = host.querySelector<HTMLDetailsElement>(".proof-state-settings");
    if (settings) state.settingsOpen = settings.open;
    const expected = host.querySelector<HTMLDetailsElement>(".proof-expected-type");
    if (expected) state.expectedOpen = expected.open;
    const messages = host.querySelector<HTMLDetailsElement>(".proof-messages");
    if (messages) state.messagesOpen = messages.open;
}

function disconnectErrorObserver(state: ProofStateHostState) {
    state.errorObserver?.disconnect();
    state.errorObserver = undefined;
}

/** Clear a proof without removing the caller's diagnostic node from the DOM. */
export function clearProofState(host: HTMLElement): void {
    const state = hostStates.get(host);
    if (state) disconnectErrorObserver(state);
    const error = state?.error ?? hostErrors.get(host);
    hostStates.delete(host);
    if (error) hostErrors.set(host, error);
    host.replaceChildren(...(error ? [error] : []));
}

function node(className: string, text?: string, tag: "div" | "span" = "div"): HTMLElement {
    const element = document.createElement(tag);
    element.className = className;
    if (text !== undefined) element.textContent = text;
    return element;
}

function appendNode(parent: HTMLElement, content: () => Node) {
    parent.appendChild(content());
}

function goalCount(goals: ProofStateGoal[]) {
    return `${goals.length} ${goals.length === 1 ? "goal" : "goals"}`;
}

function settingLabel(
    popover: HTMLElement,
    setting: keyof ProofStateSettings,
    labelText: string,
    checked: boolean,
    onChange: (value: boolean) => void
) {
    const label = document.createElement("label");
    label.className = `proof-setting proof-setting-${setting}`;
    const input = document.createElement("input");
    input.type = "checkbox";
    input.checked = checked;
    input.addEventListener("change", () => onChange(input.checked));
    label.append(input, document.createTextNode(labelText));
    popover.appendChild(label);
}

function renderExpected(
    state: ProofStateHostState,
    expected: (() => Node) | undefined
) {
    if (!expected) return null;
    const section = document.createElement("details");
    section.className = "proof-expected-type";
    setOpen(section, state.expectedOpen);
    const summary = document.createElement("summary");
    summary.className = "proof-expected-summary";
    summary.appendChild(node("proof-section-heading", "Expected type", "span"));
    section.appendChild(summary);
    const content = node("proof-expected-content");
    appendNode(content, expected);
    section.appendChild(content);
    return section;
}

function renderGoal(
    parent: HTMLElement,
    goal: ProofStateGoal,
    index: number,
    state: ProofStateHostState
) {
    const details = document.createElement("details");
    details.className = `proof-goal ${index === 0 ? "proof-goal-current" : "proof-goal-secondary"}`;
    details.setAttribute("data-proof-goal-id", goal.id);
    setOpen(details, state.goalsOpen.get(goal.id) ?? true);

    const summary = document.createElement("summary");
    summary.className = "proof-goal-summary";
    summary.appendChild(node("proof-case-label", "case", "span"));
    if (!state.settings.hideGoalNames && goal.name) {
        summary.appendChild(node("proof-goal-name", goal.name, "span"));
    }
    details.appendChild(summary);

    const body = node("proof-goal-body");
    const target = node("proof-goal-target");
    target.appendChild(node("proof-target-turnstile", "⊢"));
    appendNode(target, goal.target);
    const hypotheses = node("proof-goal-hypotheses");
    for (const hypothesis of goal.hypotheses) {
        if (state.settings.hideTypeAssumptions && hypothesis.isType) continue;
        const row = node(`proof-hypothesis${hypothesis.isType ? " proof-hypothesis-type" : ""}`);
        row.appendChild(node("proof-local-name", hypothesis.name));
        row.appendChild(document.createTextNode(" : "));
        appendNode(row, hypothesis.content);
        hypotheses.appendChild(row);
    }
    if (state.settings.targetFirst) body.append(target, hypotheses);
    else body.append(hypotheses, target);
    details.appendChild(body);
    if (index === 0 && state.settings.emphasizeFirst) details.classList.add("proof-goal-emphasized");
    parent.appendChild(details);
}

/** Render the shared Lean-style proof state used by both proof assistants. */
export function renderProofState(host: HTMLElement, options: RenderProofStateOptions): void {
    const scope = options.scope ?? "proof-state";
    const contextKey = options.contextKey ?? scope;
    let state = hostStates.get(host);
    // Callers may have cleared the host before asking for another render.
    const error = options.error ?? state?.error;
    if (state) {
        disconnectErrorObserver(state);
        if (state.scope === scope) readPreviousState(host, state);
    }
    const sharedSettings = settingsByScope.get(scope)
        ?? { ...defaultSettings, ...options.settings };
    settingsByScope.set(scope, { ...sharedSettings });
    if (!state || state.scope !== scope) {
        state = {
            scope,
            contextKey,
            rootOpen: true,
            settingsOpen: false,
            expectedOpen: true,
            messagesOpen: true,
            goalsOpen: new Map(),
            settings: { ...sharedSettings },
            lastOptions: options
        };
        hostStates.set(host, state);
    } else {
        if (state.contextKey !== contextKey) {
            state.contextKey = contextKey;
            state.goalsOpen = new Map();
        }
    }
    state.settings = { ...sharedSettings };
    state.lastOptions = options;
    state.error = error;
    if (error) hostErrors.set(host, error);
    state.goalsOpen = new Map(options.goals.map(goal =>
        [goal.id, state.goalsOpen.get(goal.id) ?? true]
    ));

    const root = document.createElement("details");
    root.className = "proof-state-root";
    setOpen(root, state.rootOpen);

    const rootSummary = document.createElement("summary");
    rootSummary.className = "proof-state-summary";
    rootSummary.appendChild(node("proof-state-title", "Tactic state", "span"));
    root.appendChild(rootSummary);

    const content = node("proof-state-content");
    const goalsHeader = node("proof-goals-header");
    goalsHeader.appendChild(node("proof-goal-count", goalCount(options.goals), "span"));
    const settings = document.createElement("details");
    settings.className = "proof-state-settings";
    setOpen(settings, state.settingsOpen);
    const settingsSummary = document.createElement("summary");
    settingsSummary.textContent = "⚙";
    settingsSummary.setAttribute("aria-label", "Proof state settings");
    settingsSummary.setAttribute("title", "Proof state settings");
    settings.appendChild(settingsSummary);
    const settingsPopover = node("proof-settings-popover");
    const updateSetting = (key: keyof ProofStateSettings, value: boolean) => {
        if (hostStates.get(host) !== state || !host.contains(settings)) return;
        settingsByScope.set(scope, { ...settingsByScope.get(scope), [key]: value });
        renderProofState(host, { ...state.lastOptions, settings: undefined });
    };
    settingLabel(settingsPopover, "targetFirst", "Target first", state.settings.targetFirst,
        value => updateSetting("targetFirst", value));
    settingLabel(settingsPopover, "hideTypeAssumptions", "Hide type assumptions", state.settings.hideTypeAssumptions,
        value => updateSetting("hideTypeAssumptions", value));
    settingLabel(settingsPopover, "hideGoalNames", "Hide goal names", state.settings.hideGoalNames,
        value => updateSetting("hideGoalNames", value));
    settingLabel(settingsPopover, "emphasizeFirst", "Emphasize current goal", state.settings.emphasizeFirst,
        value => updateSetting("emphasizeFirst", value));
    settings.appendChild(settingsPopover);
    goalsHeader.appendChild(settings);
    content.appendChild(goalsHeader);

    const goals = node("proof-goals");
    if (!options.goals.length) {
        goals.appendChild(node("proof-state-completed", options.completedText ?? "No goals"));
    } else {
        options.goals.forEach((goal, index) => renderGoal(goals, goal, index, state));
    }
    content.appendChild(goals);
    const expected = renderExpected(state, options.expected);

    root.appendChild(content);
    const messages = document.createElement("details");
    messages.className = "proof-messages";
    setOpen(messages, state.messagesOpen);
    const messagesSummary = document.createElement("summary");
    messagesSummary.className = "proof-messages-summary";
    messagesSummary.appendChild(node("proof-section-heading", "All Messages", "span"));
    const messageCount = node("proof-message-count", state.error?.textContent?.trim() ? "(1)" : "(0)", "span");
    messagesSummary.appendChild(messageCount);
    messages.appendChild(messagesSummary);
    const messagesContent = node("proof-messages-content");
    if (state.error) messagesContent.appendChild(state.error);
    messages.appendChild(messagesContent);

    host.replaceChildren(root, ...(expected ? [expected] : []), messages);

    const observedError = state.error;
    if (observedError && typeof MutationObserver === "function") {
        const observer = new MutationObserver(() => {
            if (hostStates.get(host) !== state || !host.contains(messages)
                || state.error !== observedError
                || state.errorObserver !== observer) return;
            messageCount.textContent = observedError.textContent?.trim() ? "(1)" : "(0)";
        });
        state.errorObserver = observer;
        observer.observe(observedError, {
            childList: true,
            characterData: true,
            subtree: true
        });
    }
}
