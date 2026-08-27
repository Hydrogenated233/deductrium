---
status: accepted
---

# Persist many type-theory proof pages, execute one

The type-theory proof assistant persists an ordered collection of page drafts
and tabs, but only the active page executes or replays through the
single existing assistant Worker. Giving every open draft its own live Worker,
or eagerly replaying all drafts after restoration, would make CPU and memory
cost grow with the number of tabs; inactive pages therefore retain their
state and replay lazily when activated.

A theorem row reuses its existing bound page. Editing its proposition marks
that page stale, moving it makes the page follow the theorem's current
reference scope, and deleting it detaches the page while preserving the draft;
completing a detached page appends a new theorem. Successful `qed` keeps the
current page id and position, clears its target/history/input back to a blank
target-selection state, and leaves every other draft intact. Only the page
close control removes a page and selects an adjacent page.
