# Domain Docs

This is a single-context repository. Engineering skills should read the root CONTEXT.md when it exists and any relevant decisions under docs/adr/ before changing a domain area.

Missing domain documents are not blockers. Create CONTEXT.md or an ADR only when domain terminology or an architectural decision has been established and needs to be recorded.

Use the project's existing vocabulary from CONTEXT.md in issue titles, test names, refactoring proposals, and implementation notes. If a needed concept is absent, treat that as a candidate for domain-modeling work rather than silently inventing a competing term.

For this repository, the main domain areas are the browser game, the HoTT/type-theory engine and NbE kernel, the proof assistant, theorem/folder UI state, save/load behavior, and the isolated type-theory process.
