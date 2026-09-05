---
name: autopilot
description: Start or stop the standing reminders that keep an autonomous issue-solving session on the rails. Use when the user says "start autopilot", "go autonomous on the subclauses", "go autonomous on issues above N", "stop autopilot", or asks to clear the reminders. Takes "start bysubclause", "start byissuefloor <issue-number>" or "stop".
---

# Autopilot

Seven recurring reminders, one per standing rule, that fire back into this session while it works through open issues on its own. Each rule gets its own reminder so that no rule can be quietly dropped from a merged block of text, and the fire times are staggered across the ten-minute period so they arrive one at a time rather than as a wall.

The argument selects the mode: `start bysubclause`, `start byissuefloor <issue-number>`, or `stop`.

## Start

Two forms select the work, and they differ in one reminder. `start bysubclause` takes the subclause the dependency order points at. `start byissuefloor <issue-number>` takes the open issues above the number, which are what this work has filed for itself and which the subclause resolver cannot name at all.

Create seven jobs with `CronCreate`, exactly as listed below. Use `recurring: true` (the default). Take `:01` from the form the user asked for, substituting the number they gave for `{X}` where the form carries it, and leave the other six verbatim. Each `cron` field is a distinct offset within the same ten-minute period, so the seven reminders never land together.

### The reminder that selects the work

`start bysubclause` solves the issue `next_subclause` names and nothing else. Where a defect this work files while solving that issue stops it from closing, it solves the filed issue first and returns to the subclause. Every other issue the work files is filed and left. Matching is on the canonical `Satisfy IEEE 1800-2023 §<subclause>` title, so those issues are outside this form by construction, and the one exception is bounded by the subclause in hand rather than by an issue number.

`start byissuefloor <issue-number>` runs no resolver. It works the open issues above the number, and it says nothing about which of them comes first. Nothing records an order over these issues, so the loop takes one and takes another when it closes.

The number belongs to `byissuefloor` alone. A floor applied to the subclause form would rule out every subclause there is to take, because the issue tracking a subclause was opened when the subclause was catalogued rather than when the campaign reached it, so it sits below anything the work has filed since.

Where the user named no form, what they did give still says which one. `start` alone and `start subclauses` are `bysubclause`, because a form carrying no number cannot be the one whose whole argument is a number, and `start <issue-number>` is `byissuefloor` by the same reading run backwards. `start byissuefloor` with no number is the one invocation that is missing something: ask for the number before creating anything.

Both forms fire `:01` on `1,11,21,31,41,51 * * * *`. The prompt is the whole of the difference, and it goes below in a code block rather than a table cell because the `byissuefloor` command contains the character a table row uses to end a cell.

`start bysubclause`:

```text
REMINDER: Continue autonomously, unless you need human feedback about ANYTHING — not just about what to take next. Run PYTHONPATH=.:scripts python3 -m next_subclause for the subclause in force and the issue tracking it; solve that issue whatever its number, and when it closes the same command names the next. Where a defect you file while solving that issue stops it from closing, solve what you filed first and then return to the subclause. File and leave everything else: the open issues the command does not name are not this loop's work.
```

`start byissuefloor <issue-number>`, with the number the user gave substituted for `{X}` in all three places:

```text
REMINDER: Continue autonomously, unless you need human feedback about ANYTHING — not just about what to take next. Run gh issue list --state open --limit 1000 --json number,title --jq 'map(select(.number > {X}))' for the open issues above #{X}; take one, solve it, and run the same command again when it closes. The issues at or below #{X} are a person's to take rather than this loop's.
```

### The six reminders both forms carry

| Offset | Cron | Prompt |
| --- | --- | --- |
| :02 | `2,12,22,32,42,52 * * * *` | `REMINDER: ~/LRM.pdf is the source of truth.` |
| :03 | `3,13,23,33,43,53 * * * *` | `REMINDER: Solve the issue with a single commit and push.` |
| :04 | `4,14,24,34,44,54 * * * *` | `REMINDER: Solve the issue through parallel agents, without collisions.` |
| :05 | `5,15,25,35,45,55 * * * *` | `REMINDER: After pushing, deltahdl.yml might fail at integration tests. You can ignore that.` |
| :07 | `7,17,27,37,47,57 * * * *` | `REMINDER: Do not do anything but wait while a workflow is running.` |
| :09 | `9,19,29,39,49,59 * * * *` | `REMINDER: When you come up against a new problem, file a GitHub issue.` |

### What to report

Then run the form's own selector once and tell the user where the work stands.

For `start bysubclause`, run `PYTHONPATH=.:scripts python3 -m next_subclause` and name the subclause and issue it printed.

For `start byissuefloor <issue-number>`, run the `gh issue list` command from that form's prompt and name the floor it was given, how many open issues stand above it, and which of them the first iteration will take.

Either way, a selector that names nothing is where this stops: say so and do not create the jobs, because every firing would report the same. Otherwise say that seven reminders are running and give the two limits that come with them — the jobs live in this session only and are gone when it ends, and recurring jobs auto-expire after seven days.

Then start the first iteration in the same turn, without waiting for a reminder to arrive. Take the issue the selector named, or one of the issues it listed, and begin solving it under the seven prompts listed above.

## Stop

Call `CronList`, then call `CronDelete` once per job it returns — all of them, not only the seven this skill created. "Delete all your reminders" means the session ends with an empty schedule. Call `CronList` again afterwards to confirm it is empty, and report how many jobs were deleted.

`CronList` returning nothing is not a failure; say the schedule was already empty and stop.

## Notes

Cron jobs fire only while the session is idle, never mid-turn, because a turn cannot be preempted. That limit is the reason this skill does not try to correct drift in the middle of a task: what it can do is restart a loop that has stalled, which is the failure it is there to catch.

Starting the reminders starts the work, in the same turn. It used to end the turn instead and leave the first iteration to the first firing, which spent up to ten minutes on an idle session and needed nothing that was not in context already: this file lists all seven prompts, and invoking the skill is what reads them in. A reminder restarts a loop that has stalled, so until a first iteration has run there is no loop for one to restart.

Each form is named rather than inferred from whether a number was given. The floor came back in the shape it had before `70f1e9899`, where the number alone selected the form, and that commit had already found what is wrong with it: `start 2939` says nothing about what the loop will take, and a caller who means the floor form and forgets the number silently gets the other one. A name says which set is being asked for, and leaves the number to mean only how much of it.

The floor is an argument rather than a constant because the set it bounds has no boundary written down anywhere. It was fixed at 2939 for one commit, on the grounds that every open issue above 2939 sat in one blocked-by sequence; that sequence is not something this repository keeps any more, so 2939 names nothing now, and no other number does either. Which of the issues this work has filed for itself are worth taking is a judgement about the backlog on the day, and the caller is who makes it.

`start bysubclause` takes one issue beyond the subclause, and that one is bounded by the subclause rather than by a number: a defect filed while solving it that stops it from closing. Bounding it that way is what keeps the form from reading as an instruction to work the backlog, since a number would select issues by when they were filed, which says nothing about whether the subclause can close without them. Where the caller does want the backlog worked, `start byissuefloor` is the form that says so, and it says it instead of the subclause rather than alongside it — a loop is worth having where it selects one set, and two forms are worth having where each names its own.

`start byissuefloor` exists because the subclause selector cannot reach the issues the work files for itself. `issue_title_for` in `lib/python/github/__init__.py` builds `Satisfy IEEE 1800-2023 §<subclause>`, and `next_subclause` looks issues up by that string alone, while those issues are titled by the defect they describe. So no run of the command will ever name one, whatever the campaign does next, and an issue number is the only handle the skill has on them. It is a weaker handle than the one the subclauses get: `next_subclause` answers from a recorded dependency order, while a floor says only which issues are in scope.

The first reminder of either form names a command rather than an issue, and both halves of that matter. A cron prompt is fixed when the job is created while the work moves on without it, so a reminder naming the issue it started on would be wrong before the session ended and would say nothing about it. And an instruction to work through the open issues has only one way of being obeyed — read them all, then choose — which costs the whole backlog on every choice and grows with each issue the work files for itself. Both prompts name a query instead: `next_subclause` answers from the dependency order, which cannot be wrong about what has to come first, and the `gh issue list` filter answers from the floor, which is what keeps the listing from being the whole backlog. Where the subclause form gets an order out of that, the floor form gets a set and chooses within it. What `next_subclause` matches on and why is in its own docstrings.

Reminder :04 names parallel agents because that is what solves an issue here, and the collision it rules out is two agents writing one file or two agents pushing where the run needs one push. It replaced two reminders that named a list of indivisible Claude tasks. Splitting one rule across two reminders bought nothing, and the list was never what did the work.

No reminder tells the loop to compact, because a session cannot compact itself. `/compact` is a built-in Claude Code command whose behaviour is coded into the CLI rather than a bundled skill handed to Claude, so the person at the keyboard is the only one who can run it, and the commands reference at <https://code.claude.com/docs/en/commands> names no tool, hook or flag that would let a session run it. What frees a long session's context instead is the auto-compact window at <https://code.claude.com/docs/en/model-config#set-the-auto-compact-window>, which Claude Code applies on its own as the conversation approaches the context limit. A `:06` reminder to compact before starting an issue was created and then removed for that reason: every firing of it asked for something no iteration of the loop could do, and spent a turn saying so.

Reminder :05 exists because `.github/workflows/deltahdl.yml` is red on every push and that is the standing state rather than a break. `scripts/run_sv_tests/__init__.py` ends in `sys.exit(min(failed, 1))`, so the `integration-test-coverage` job fails while any sv-test does, and 146 of 830 do. Issues #2910 through #2939 track those failures. Without the reminder, the standing instruction in `.claude/CLAUDE.md` to fix a red run in the session that finds it sends every iteration of the loop at the same 146 tests it was not started to fix.
