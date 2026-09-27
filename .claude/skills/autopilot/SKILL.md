---
name: autopilot
description: Start, restart or stop the standing reminders, with or without the loop that works through open issues. Use when the user says "start autopilot", "go autonomous on the subclauses", "go autonomous on issues above N", "go autonomous on the §5 issues", "reminders on", "reminders only", "stop autopilot", "reminders off", or asks to clear the reminders or to switch from one form to another ("restart autopilot", "switch to reminders only"). Takes "start bysubclause", "start byissuefloor <issue-number>", "start bylabel <label>", "start reminders-only", the same four forms after "restart", or "stop"; every "start" or "restart" form but "reminders-only" also takes `--skip-label <label>`, repeatable.
---

# Autopilot

## The seven standing reminders

Every `start` form creates these.

| Cron | Prompt |
| --- | --- |
| `0,20,40 * * * *` | `REMINDER: Work through a set of indivisible tasks, written down with TaskCreate before the work starts and marked with TaskUpdate as each one starts and finishes.` |
| `2,22,42 * * * *` | `REMINDER: ~/IEEE 1800-2023.pdf is the source of truth. sv-tests was written against ~/IEEE 1800-2017.pdf, so its tags and file names carry 2017 clause numbers: read the 2017 edition only to learn what such a number meant there, resolve it to the 2023 clause, and let no 2017 number, wording or rule reach deltahdl's code, reports or tests. The UVM standard is ~/IEEE 1800.2-2020.pdf.` |
| `3,23,43 * * * *` | `REMINDER: Let every push carry exactly one commit, and let that commit hold a whole body of work: a matter solved end to end or carried out in full, or a batch of every open issue of one matter (one clause of IEEE 1800-2023 fixed in one subsystem under src/), bounded by the matter and never by a count.` |
| `6,26,46 * * * *` | `REMINDER: Keep the task list itself current, not only the marks on it: a task that arises is added the moment it does, a task that turns out unneeded is removed, and a task whose shape changed is rewritten, so that the list always says what is left to do.` |
| `7,27,47 * * * *` | `REMINDER: While any CI run for a pushed commit is in progress, only wait: no diagnosis, edits or commits.` |
| `8,28,48 * * * *` | `REMINDER: Solve what you find rather than filing it and moving on.` |
| `9,29,49 * * * *` | `REMINDER: Ensure every task on the list is indivisible, whether it was written with TaskCreate or rewritten with TaskUpdate: read each subject as written and count the actions it names; a subject naming more than one action is divisible, whatever single purpose those actions serve, and is split into one task per action.` |

## The three loop reminders

Every `start` form but `reminders-only` adds these.

On `1,21,41 * * * *`, by form:

`start bysubclause`:

```text
REMINDER: Run gh issue list --state open --limit 1000 --json number,title --jq 'map(select(.title | test("^Satisfy IEEE 1800-2023 §([A-Z]|[0-9]+)(\\.[0-9]+)*$")) | .subclause = (.title | ltrimstr("Satisfy IEEE 1800-2023 §"))) | sort_by((.subclause | split(".") | map(tonumber? // .)), .number) | (first.subclause // "" | split(".") | first) as $c | map(select(.subclause | split(".") | first == $c)) | .[] | "§\(.subclause) #\(.number)"' for the lowest subclause with an open issue tracking it, followed by the other open subclauses of its clause, each with its issue's number. Solve the first of them whatever its number, together with those of the rest whose fixes land in its subsystem under src/, as one batch pushed as one commit; when they close, the same command names the next. The open issues the command does not name are not this loop's work.
```

`start byissuefloor <issue-number>`:

```text
REMINDER: Run gh issue list --state open --limit 1000 --json number,title,labels --jq 'map(select(.number > {X}) | {number, title, labels: [.labels[].name]})' for the open issues above #{X}; take one, together with every other issue in the list of its matter (its clause label, fixed in its subsystem under src/), as one batch pushed as one commit, and run the same command again when they close. The issues at or below #{X} are a person's to take rather than this loop's.
```

`start bylabel <label>`:

```text
REMINDER: Run gh issue list --state open --label '{L}' --limit 1000 --json number,title,labels --jq 'map({number, title, labels: [.labels[].name]})' for the open issues labelled '{L}'; take one, together with every other issue in the list of its matter (its clause, fixed in its subsystem under src/), as one batch pushed as one commit, and run the same command again when they close. The open issues without the label '{L}' are not this loop's work.
```

And these:

| Cron | Prompt |
| --- | --- |
| `4,24,44 * * * *` | `REMINDER: Continue autonomously, unless you need human feedback about ANYTHING — not just about what to take next. When you do, rewrite the issue's title if necessary, rewrite the issue's body, label the issue 'needs decision', and move on to the next issue.` |
| `5,25,45 * * * *` | `REMINDER: Before working on an issue, ensure the issue is up to date. If it is outdated, rewrite its title and body as necessary, delete all its comments, and ensure its labels are correct.` |

## Start

`start` alone is `bysubclause`, `start <issue-number>` is `byissuefloor`, and `start §5` is `bylabel`.

Any form but `reminders-only` may be followed by `--skip-label <label>`, once per label, quoted when it holds a space. Each adds to the loop's `gh issue list` command, right after `--state open`, a `-label:"<label>"` term in one `--search` flag — `--search '-label:"needs decision" -label:"blocked"'` — and appends to that reminder, after a space, `An issue labelled '<label>' is left to a person, whatever else it carries.`

For any form but `reminders-only`, run the loop's `gh issue list` command once; if it names no issue, create the seven standing reminders only.

Call `CronList`. A job on one of the form's cron slots whose prompt differs from that slot's reminder is a stale version of it: `CronDelete` it. Then `CronCreate` with `recurring: true` each reminder of the form whose prompt is not already scheduled, substituting the number for `{X}` or the label for `{L}`. Then begin solving the batch the command's first issue seeds.

## Restart

`restart` takes the forms `start` takes, with the same shorthands and the same `--skip-label` flags, and leaves scheduled exactly the reminders of the form it names, whatever was scheduled before.

For any form but `reminders-only`, run the loop's `gh issue list` command once; if it names no issue, the form's reminders are the seven standing reminders only.

Call `CronList`. `CronDelete` every job that is not one of the form's reminders: a job on a slot the form does not use, a job whose prompt differs from its slot's reminder, and every job but one on a slot that holds more than one. Then `CronCreate` with `recurring: true` each reminder of the form whose prompt is not scheduled after those deletions, substituting the number for `{X}` or the label for `{L}`. Then, for any form but `reminders-only`, begin solving the batch the command's first issue seeds.

## Batches

A loop takes a batch, not a single issue: the issue its command names first, with every open issue it lists of the same matter, meaning the same clause of IEEE 1800-2023 fixed in the same subsystem under `src/`. The batch is solved in the working tree and pushed as one commit with one `Closes #N` line per issue. `.claude/memories/grouping-issues-into-a-push.md` gives the rule in full: why the matter bounds the batch rather than a count, which changes go in a push of their own, and how a red run is traced back to an issue.

## Stop

Call `CronList`, then `CronDelete` for every job it returns.
