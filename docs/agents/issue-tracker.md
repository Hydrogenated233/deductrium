# Issue Tracker: GitHub

Issues and specifications for this repository live in GitHub Issues at Hydrogenated233/deductrium. Use the gh CLI for issue operations.

## Conventions

- Create: `gh issue create --title "..." --body "..."`
- Read: `gh issue view <number> --comments`
- List: `gh issue list --state open --json number,title,body,labels,comments`
- Comment: `gh issue comment <number> --body "..."`
- Add or remove labels: `gh issue edit <number> --add-label "..."` or `--remove-label "..."`
- Close: `gh issue close <number> --comment "..."`

PRs are not treated as a triage request surface by default. Resolve ambiguous #N references by checking the pull request and issue views.

When an engineering skill says to publish to the issue tracker, create or update a GitHub issue. When it asks for a relevant ticket, run `gh issue view <number> --comments`.
