---
name: autopilot
description: Start or stop the standing reminders, with or without the loop that works through open issues. Use when the user says "start autopilot", "go autonomous on the subclauses", "go autonomous on issues above N", "go autonomous on the §5 issues", "reminders on", "reminders only", "stop autopilot", "reminders off", or asks to clear the reminders. Takes "start bysubclause", "start byissuefloor <issue-number>", "start bylabel <label>", "start reminders-only" or "stop"; every "start" form but "reminders-only" also takes `--skip-label <label>`, repeatable.
---

# Autopilot

## The seven standing reminders

Every `start` form creates these:

| Cron | Prompt |
| --- | --- |
| `0,10,20,30,40,50 * * * *` | `REMINDER: Work through a set of indivisible tasks, written down with TaskCreate before the work starts and marked with TaskUpdate as each one starts and finishes.` |
| `2,12,22,32,42,52 * * * *` | `REMINDER: ~/IEEE 1800-2023.pdf is the source of truth. sv-tests was written against ~/IEEE 1800-2017.pdf, so its tags and file names carry 2017 clause numbers: read the 2017 edition only to learn what such a number meant there, resolve it to the 2023 clause, and let no 2017 number, wording or rule reach deltahdl's code, reports or tests.` |
| `3,13,23,33,43,53 * * * *` | `REMINDER: Solve the issue with a single commit and push.` |
| `6,16,26,36,46,56 * * * *` | `REMINDER: Keep the task list itself current, not only the marks on it: a task that arises is added the moment it does, a task that turns out unneeded is removed, and a task whose shape changed is rewritten, so that the list always says what is left to do.` |
| `7,17,27,37,47,57 * * * *` | `REMINDER: Do not do anything but wait while a workflow is running.` |
| `8,18,28,38,48,58 * * * *` | `REMINDER: Solve what you find rather than filing it and moving on. A failing integration test in deltahdl.yml is the exception: leave that one where it is.` |
| `9,19,29,39,49,59 * * * *` | `REMINDER: Ensure every task on the list is indivisible, whether it was written with TaskCreate or rewritten with TaskUpdate: read each subject as written and count the actions it names; a subject naming more than one action is divisible, whatever single purpose those actions serve, and is split into one task per action.` |

## The three loop reminders

Every `start` form but `reminders-only` adds these.

On `1,11,21,31,41,51 * * * *`, by form:

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

And these two:

| Cron | Prompt |
| --- | --- |
| `4,14,24,34,44,54 * * * *` | `REMINDER: Continue autonomously, unless you need human feedback about ANYTHING — not just about what to take next. When you do, write the question as a comment on the issue, label the issue 'needs decision', and move on to the next issue.` |
| `5,15,25,35,45,55 * * * *` | `REMINDER: After pushing, deltahdl.yml might fail at its integration tests. You can ignore that.` |

## Start

- `start bysubclause` — the lowest subclause with an open `Satisfy IEEE 1800-2023 §<subclause>` issue.
- `start byissuefloor <issue-number>` — the open issues above the number.
- `start bylabel <label>` — the open issues carrying the label, exactly as written; `gh label list` prints them.
- `start reminders-only` — the seven standing reminders alone.

`start` alone is `bysubclause`, `start <issue-number>` is `byissuefloor`, and `start §5` is `bylabel`. A form missing its argument: ask for it before creating anything.

Any form but `reminders-only` may be followed by `--skip-label <label>`, once per label, quoted when it holds a space. Each adds to the loop's `gh issue list` command, right after `--state open`, a `-label:"<label>"` term in one `--search` flag — `--search '-label:"needs decision" -label:"blocked"'` — and appends to that reminder, after a space, `An issue labelled '<label>' is left to a person, whatever else it carries.`

For any form but `reminders-only`, run the loop's `gh issue list` command once and name what it printed: the subclause and issue for `bysubclause`; the floor or label, how many open issues it selects, and which one the first iteration takes for the other two; and the labels skipped. If it names nothing, say so and create the seven standing reminders only.

Call `CronList`, then `CronCreate` with `recurring: true` for each reminder of the form whose prompt is not already scheduled, substituting the number for `{X}` or the label for `{L}`. Report which were created and which were already running, that they live in this session only, and that recurring jobs expire after seven days. Then begin solving the issue named in the same turn, or, when none was, carry on with whatever the session was doing.

## Stop

Call `CronList`, then `CronDelete` for every job it returns. Call `CronList` again to confirm it is empty and report how many were deleted.
