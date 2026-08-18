---
name: autopilot
description: Start or stop the standing reminders that keep an autonomous issue-solving session on the rails. Use when the user says "start autopilot", "go autonomous on issues above N", "stop autopilot", or asks to clear the reminders. Takes "start <issue-number>", "start sequence" or "stop".
---

# Autopilot

Eight recurring reminders, one per standing rule, that fire back into this session while it works through open issues on its own. Each rule gets its own reminder so that no rule can be quietly dropped from a merged block of text, and the fire times are staggered across the ten-minute period so they arrive one at a time rather than as a wall.

The argument selects the mode: `start <issue-number>`, `start sequence`, or `stop`.

## Start

Two forms select the work, and they differ in one reminder. `start <issue-number>` takes the subclause the dependency order points at. `start sequence` takes the issues above 2939, which the subclause resolver cannot name at all.

Create eight jobs with `CronCreate`, exactly as listed below. Use `recurring: true` (the default). Take `:01` from the form the user asked for and leave the other seven verbatim. Each `cron` field is a distinct offset within the same ten-minute period, so the eight reminders never land together.

### The reminder that selects the work

`start <issue-number>` requires the number — it is the `{X}` below. If the user gave neither a number nor `sequence`, ask which form they want before creating anything.

The number bounds the issues the resolver does not name, and only those. The issue tracking a subclause was opened when that subclause was catalogued rather than when the campaign reached it, so it sits below anything the work has filed since; a floor applied to it would rule out every subclause there is to take. What the floor is for is the other direction — the issues this work opens as it goes, which accumulate without limit and are the ones worth bounding.

`start sequence` takes no number. Everything above 2939 is in the sequence by the rule that defines it, so there is nothing left for a floor to select.

| Form | Cron | Prompt |
| --- | --- | --- |
| `start <issue-number>` | `1,11,21,31,41,51 * * * *` | `REMINDER: Continue autonomously, unless you need human feedback about ANYTHING — not just about what to take next. Run PYTHONPATH=.:scripts python3 -m next_subclause for the subclause in force and the issue tracking it; solve that issue whatever its number, and when it closes the same command names the next. Among the issues it does not name, the ones above #{X} are in scope alongside it and are what this work has filed for itself; the ones at or below #{X} are not.` |
| `start sequence` | `1,11,21,31,41,51 * * * *` | `REMINDER: Continue autonomously, unless you need human feedback about ANYTHING — not just about what to take next. Run the sequence walk in docs/claude/issue-blocked-by-sequence.md and solve the single open issue it reports as the head. When that issue closes, run the walk again for the next one.` |

### The seven reminders both forms carry

| Offset | Cron | Prompt |
| --- | --- | --- |
| :02 | `2,12,22,32,42,52 * * * *` | `REMINDER: ~/LRM.pdf is the source of truth.` |
| :03 | `3,13,23,33,43,53 * * * *` | `REMINDER: Solve the issue with a single commit and push.` |
| :04 | `4,14,24,34,44,54 * * * *` | `REMINDER: Solve the issue through parallel agents, without collisions.` |
| :05 | `5,15,25,35,45,55 * * * *` | `REMINDER: After pushing, deltahdl.yml might fail at integration tests. You can ignore that.` |
| :06 | `6,16,26,36,46,56 * * * *` | `REMINDER: Compact the conversation before you start solving an issue.` |
| :07 | `7,17,27,37,47,57 * * * *` | `REMINDER: Do not do anything but wait while a workflow is running.` |
| :09 | `9,19,29,39,49,59 * * * *` | `REMINDER: When you come up against a new problem, file a GitHub issue. A problem in the program — src/, lib/, scripts/, and the machinery under test/ — gets the sub-headers "Problem", "Why Unit Tests Did Not Catch It?", "Why Integration Tests Did Not Catch It?", "Why E2E Tests Did Not Catch It?", "Which Unit, Integration, or E2E regression tests would prevent this from happening again?", and "Proposed Solution". A problem in a workflow file, a linter configuration, a build file or the docs gets "Problem" and "Proposed Solution" only, and owes no tests.` |

### What to report

Then run the selector once and tell the user where the work stands.

For `start <issue-number>`, run `PYTHONPATH=.:scripts python3 -m next_subclause` and name the subclause and issue it printed, and which issue number is the floor. If the command reports there is nothing tracked, say so; the reminders are still worth starting, because the floor still selects work.

For `start sequence`, run the walk in [issue-blocked-by-sequence](../../../docs/claude/issue-blocked-by-sequence.md) and name the head it reported. If it reports anything but one head, say so and do not start the reminders: the sequence is broken, and a loop taking its head would take an arbitrary one of several.

Either way, say that eight reminders are running and give the two limits that come with them — the jobs live in this session only and are gone when it ends, and recurring jobs auto-expire after seven days.

Do not begin working the issues as part of starting the reminders. Starting autopilot and doing the work are separate; the first reminder will arrive within ten minutes and start the loop, unless the user asks to begin straight away.

## Stop

Call `CronList`, then call `CronDelete` once per job it returns — all of them, not only the eight this skill created. "Delete all your reminders" means the session ends with an empty schedule. Call `CronList` again afterwards to confirm it is empty, and report how many jobs were deleted.

`CronList` returning nothing is not a failure; say the schedule was already empty and stop.

## Notes

Cron jobs fire only while the session is idle, never mid-turn, because a turn cannot be preempted. That limit is the reason this skill does not try to correct drift in the middle of a task: what it can do is restart a loop that has stalled, which is the failure it is there to catch.

`start sequence` exists because the subclause resolver cannot reach the issues above 2939. `issue_title_for` in `lib/python/github/__init__.py` builds `Satisfy IEEE 1800-2023 §<subclause>`, and `next_subclause` looks issues up by that string alone. The issues the work files for itself are titled by the defect they describe, so no run of the command will ever name one, whatever the campaign does next. `docs/claude/issue-blocked-by-sequence.md` holds the order that does reach them: every open issue above 2939 sits in one linear sequence, exactly one is blocked by nothing open, and that one is what gets worked next.

The first reminder of either form names a command rather than an issue, and both halves of that matter. A cron prompt is fixed when the job is created while the work moves on without it, so a reminder naming the issue it started on would be wrong before the session ended and would say nothing about it. And an instruction to work through the open issues has only one way of being obeyed — read them all, then choose — which costs the whole backlog on every choice and grows with each issue the work files for itself. Both selectors answer instead from a recorded order, which cannot be wrong about what has to come first. What `next_subclause` matches on and why is in its own docstrings.

Reminder :04 names parallel agents because that is what solves an issue here, and the collision it rules out is two agents writing one file or two agents pushing where the run needs one push. It replaced two reminders that named a list of indivisible Claude tasks. Splitting one rule across two reminders bought nothing, and the list was never what did the work.

Reminder :06 fires at the boundary between issues because that is the only point where the finished issue's context is safe to drop. A loop that solves one issue after another keeps every file it read and every run it waited on, so the window it starts the next issue with is the window the last issue left rather than an empty one. Compacting there costs nothing the next issue needs.

Reminder :05 exists because `.github/workflows/deltahdl.yml` is red on every push and that is the standing state rather than a break. `scripts/run_sv_tests/__init__.py` ends in `sys.exit(min(failed, 1))`, so the `integration-test-coverage` job fails while any sv-test does, and 146 of 830 do. Issues #2910 through #2939 track those failures. Without the reminder, `docs/claude/inheriting-a-red-gate.md` sends every iteration of the loop at the same 146 tests it was not started to fix.

The issue sub-headers in the last reminder are the user's wording. `CLAUDE.md` carries the same six sections, the regression one included, and `docs/claude/how-issues-are-written.md` is the authority when an issue is actually being written. All three name the sections identically, `Proposed Solution` included.

That reminder carries the two-section form as well as the six, because it used to carry only the six and firing them alone every ten minutes was enough to produce the tests they asked for. A defect in a workflow file or a linter configuration was arriving beside a standing instruction to name the regression tests that would prevent it, and the instruction won: an issue over three copies of one yamllint rule set answered all four test sections and asked for two unit tests over a reading that would exist only because the rule set is written three times. A reminder that names only one case is read as though that case were the whole rule.
