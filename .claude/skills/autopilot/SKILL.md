---
name: autopilot
description: Start or stop the standing reminders, with or without the loop that works through open issues. Use when the user says "start autopilot", "go autonomous on the subclauses", "go autonomous on issues above N", "go autonomous on the §5 issues", "reminders on", "reminders only", "stop autopilot", "reminders off", or asks to clear the reminders. Takes "start bysubclause", "start byissuefloor <issue-number>", "start bylabel <label>", "start reminders-only" or "stop"; every "start" form but "reminders-only" also takes `--skip-label <label>`, repeatable.
---

# Autopilot

## The seven standing reminders

Every `start` form creates these.

| Cron | Prompt |
| --- | --- |
| `0,20,40 * * * *` | `REMINDER: Work through a set of indivisible tasks, written down with TaskCreate before the work starts and marked with TaskUpdate as each one starts and finishes.` |
| `2,22,42 * * * *` | `REMINDER: ~/IEEE 1800-2023.pdf is the source of truth. sv-tests was written against ~/IEEE 1800-2017.pdf, so its tags and file names carry 2017 clause numbers: read the 2017 edition only to learn what such a number meant there, resolve it to the 2023 clause, and let no 2017 number, wording or rule reach deltahdl's code, reports or tests. The UVM standard is ~/IEEE 1800.2-2020.pdf.` |
| `3,23,43 * * * *` | `REMINDER: Let every push carry exactly one commit, and let that commit hold a whole body of work: an issue solved end to end, or a request of the user's carried out in full.` |
| `6,26,46 * * * *` | `REMINDER: Keep the task list itself current, not only the marks on it: a task that arises is added the moment it does, a task that turns out unneeded is removed, and a task whose shape changed is rewritten, so that the list always says what is left to do.` |
| `7,27,47 * * * *` | `REMINDER: While any CI run for a pushed commit is in progress, only wait: no diagnosis, edits or commits.` |
| `8,28,48 * * * *` | `REMINDER: Solve what you find rather than filing it and moving on.` |
| `9,29,49 * * * *` | `REMINDER: Ensure every task on the list is indivisible, whether it was written with TaskCreate or rewritten with TaskUpdate: read each subject as written and count the actions it names; a subject naming more than one action is divisible, whatever single purpose those actions serve, and is split into one task per action.` |

## The two loop reminders

Every `start` form but `reminders-only` adds these.

On `1,21,41 * * * *`, by form:

`start bysubclause`:

```text
REMINDER: Run gh issue list --state open --limit 1000 --json number,title --jq 'map(select(.title | test("^Satisfy IEEE 1800-2023 §([A-Z]|[0-9]+)(\\.[0-9]+)*$")) | .subclause = (.title | ltrimstr("Satisfy IEEE 1800-2023 §"))) | sort_by((.subclause | split(".") | map(tonumber? // .)), .number) | first // empty | "§\(.subclause) #\(.number)"' for the lowest subclause with an open issue tracking it and that issue's number; solve that issue whatever its number, and when it closes the same command names the next. The open issues the command does not name are not this loop's work.
```

`start byissuefloor <issue-number>`:

```text
REMINDER: Run gh issue list --state open --limit 1000 --json number,title --jq 'map(select(.number > {X}))' for the open issues above #{X}; take one, solve it, and run the same command again when it closes. The issues at or below #{X} are a person's to take rather than this loop's.
```

`start bylabel <label>`:

```text
REMINDER: Run gh issue list --state open --label '{L}' --limit 1000 --json number,title for the open issues labelled '{L}'; take one, solve it, and run the same command again when it closes. The open issues without the label '{L}' are not this loop's work.
```

And this one:

| Cron | Prompt |
| --- | --- |
| `4,24,44 * * * *` | `REMINDER: Continue autonomously, unless you need human feedback about ANYTHING — not just about what to take next. When you do, write the question as a comment on the issue, label the issue 'needs decision', and move on to the next issue.` |

## Start

`start` alone is `bysubclause`, `start <issue-number>` is `byissuefloor`, and `start §5` is `bylabel`.

Any form but `reminders-only` may be followed by `--skip-label <label>`, once per label, quoted when it holds a space. Each adds to the loop's `gh issue list` command, right after `--state open`, a `-label:"<label>"` term in one `--search` flag — `--search '-label:"needs decision" -label:"blocked"'` — and appends to that reminder, after a space, `An issue labelled '<label>' is left to a person, whatever else it carries.`

For any form but `reminders-only`, run the loop's `gh issue list` command once; if it names no issue, create the seven standing reminders only.

Call `CronList`, then `CronCreate` with `recurring: true` for each reminder of the form whose prompt is not already scheduled, substituting the number for `{X}` or the label for `{L}`. Then begin solving the issue the command named.

## Stop

Call `CronList`, then `CronDelete` for every job it returns.
