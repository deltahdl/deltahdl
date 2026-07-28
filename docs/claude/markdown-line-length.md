# Where the 80-column Markdown rule applies

`.github/workflows/documentation.yml` runs `markdownlint '**/*.md'` with
no configuration file — inline disables and config files are both
asserted absent — so MD013 holds at its default of 80 characters. Every
tracked `.md` file in the repository is hard-wrapped to fit it.

That rule is a property of the linter, not of Markdown. It stops at the
working tree.

GitHub issue and pull-request bodies, issue comments, and commit-message
bodies are not linted by anything, and GitHub reflows them to the reader's
window. Hard-wrapping them buys nothing and costs: a wrapped body is
harder to edit, and quoting a sentence out of it drags line breaks along.
Write issue prose as one line per paragraph and let the browser wrap it.
Code blocks inside an issue keep their own line breaks, since those are
significant.

Open issues above #2794 were rewritten this way on 2026-07-27 after the
80-column habit leaked from `docs/` into issue bodies: #2841, #2842 (body
and comment), #2845, #2846 and #2847.
