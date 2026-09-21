---
name: autopilot
description: Start or stop the standing reminders that keep an autonomous issue-solving session on the rails. Use when the user says "start autopilot", "go autonomous on the subclauses", "go autonomous on issues above N", "go autonomous on the §5 issues", "stop autopilot", or asks to clear the reminders. Takes "start bysubclause", "start byissuefloor <issue-number>", "start bylabel <label>" or "stop"; every "start" form also takes `--skip-label <label>`, repeatable, naming a label whose issues the loop leaves alone.
---

# Autopilot

Ten recurring reminders, one rule each, that fire back into this session while it works through open issues on its own. Cron jobs fire only while the session is idle, so a reminder restarts a loop that has stalled; the offsets are staggered so the ten never land together.

## Start

The form names the set of issues to work, and only the `:01` reminder differs between forms:

- `start bysubclause` — the lowest subclause with an open `Satisfy IEEE 1800-2023 §<subclause>` issue.
- `start byissuefloor <issue-number>` — the open issues above the number.
- `start bylabel <label>` — the open issues carrying the label, exactly as written; `gh label list` prints them, the clause labels being `§1` through `§41`, `Annex A` and `Annex B`.

`start` alone is `bysubclause`, `start <issue-number>` is `byissuefloor`, and `start §5` is `bylabel`. `start byissuefloor` with no number and `start bylabel` with no label are missing their argument: ask for it before creating anything.

Any form may be followed by `--skip-label <label>`, once per label, naming a label whose issues the loop must not take — `start bylabel §5 --skip-label "needs decision"` leaves every §5 issue that also carries `needs decision` to a person. A label with a space in it is quoted. `gh issue list` has no flag that excludes a label; the exclusion is a `--search` query, so with `--skip-label` the `:01` command gains, right after `--state open`, one `--search` flag holding one `-label:"<label>"` term per label, such as `--search '-label:"needs decision"'` or `--search '-label:"needs decision" -label:"blocked"'`, and the reminder ends with one extra sentence after a space: `An issue labelled '<label>' is left to a person, whatever else it carries.` — one such sentence per label. A `--skip-label` with no label is missing its argument: ask for it before creating anything.

Create ten jobs with `CronCreate`, `recurring: true`. Take `:01` from the form asked for, substituting the number for `{X}` or the label for `{L}` wherever it appears and adding the `--skip-label` search and sentences when they were asked for, and the other nine verbatim.

### The `:01` reminder, on `1,11,21,31,41,51 * * * *`

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

### The nine reminders every form carries

| Offset | Cron | Prompt |
| --- | --- | --- |
| :00 | `0,10,20,30,40,50 * * * *` | `REMINDER: Work through a set of indivisible tasks, written down with TaskCreate before the work starts and marked with TaskUpdate as each one starts and finishes.` |
| :02 | `2,12,22,32,42,52 * * * *` | `REMINDER: ~/IEEE 1800-2023.pdf is the source of truth.` |
| :03 | `3,13,23,33,43,53 * * * *` | `REMINDER: Solve the issue with a single commit and push.` |
| :04 | `4,14,24,34,44,54 * * * *` | `REMINDER: Continue autonomously, unless you need human feedback about ANYTHING — not just about what to take next. When you do, write the question as a comment on the issue, label the issue 'needs decision', and move on to the next issue.` |
| :05 | `5,15,25,35,45,55 * * * *` | `REMINDER: After pushing, deltahdl.yml might fail at its integration tests. You can ignore that.` |
| :06 | `6,16,26,36,46,56 * * * *` | `REMINDER: Keep the task list itself current, not only the marks on it: a task that arises is added the moment it does, a task that turns out unneeded is removed, and a task whose shape changed is rewritten, so that the list always says what is left to do.` |
| :07 | `7,17,27,37,47,57 * * * *` | `REMINDER: Do not do anything but wait while a workflow is running.` |
| :08 | `8,18,28,38,48,58 * * * *` | `REMINDER: Solve what you find rather than filing it and moving on. A failing integration test in deltahdl.yml is the exception: leave that one where it is.` |
| :09 | `9,19,29,39,49,59 * * * *` | `REMINDER: Ensure every task on the list is indivisible, whether it was written with TaskCreate or rewritten with TaskUpdate: read each subject as written and count the actions it names; a subject naming more than one action is divisible, whatever single purpose those actions serve, and is split into one task per action.` |

### Report and begin

Run the form's `gh issue list` command once, with its `--search` exclusion when `--skip-label` was given. Name what it printed: the subclause and issue for `bysubclause`; the floor or label, how many open issues it selects, and which one the first iteration takes for the other two; and, when labels are skipped, which they are. If it names nothing, say so and create no jobs.

Otherwise say that ten reminders are running, that they live in this session only, and that recurring jobs expire after seven days. Then start the first iteration in the same turn: take the issue the command named and begin solving it under the ten prompts above.

## Stop

Call `CronList`, then `CronDelete` for every job it returns, not only this skill's. Call `CronList` again to confirm it is empty and report how many were deleted. An already-empty schedule is not a failure; say so.
