---
name: autopilot
description: Start or stop the standing reminders that keep an autonomous issue-solving session on the rails. Use when the user says "start autopilot", "go autonomous on the subclauses", "stop autopilot", or asks to clear the reminders. Takes "start" or "stop".
---

# Autopilot

Seven recurring reminders, one per standing rule, that fire back into this session while it works through open issues on its own. Each rule gets its own reminder so that no rule can be quietly dropped from a merged block of text, and the fire times are staggered across the ten-minute period so they arrive one at a time rather than as a wall.

The argument selects the mode: `start` or `stop`. `start subclauses` asks for the same thing, since the subclause is the only work this skill selects.

## Start

The work is the subclause the dependency order points at, and `next_subclause` is what names it. The skill takes no issue number: reminder :01 names that command rather than an issue.

Create seven jobs with `CronCreate`, exactly as listed below. Use `recurring: true` (the default) and leave every prompt verbatim. Each `cron` field is a distinct offset within the same ten-minute period, so the seven reminders never land together.

Reminder :01 solves the issue `next_subclause` names. Where a defect this work files while solving that issue stops it from closing, it solves the filed issue first and returns to the subclause. Every other issue the work files is filed and left. Matching is on the canonical `Satisfy IEEE 1800-2023 §<subclause>` title, so those issues are outside the loop by construction, and the one exception is bounded by the subclause in hand rather than by an issue number.

### The seven reminders

| Offset | Cron | Prompt |
| --- | --- | --- |
| :01 | `1,11,21,31,41,51 * * * *` | `REMINDER: Continue autonomously, unless you need human feedback about ANYTHING — not just about what to take next. Run PYTHONPATH=.:scripts python3 -m next_subclause for the subclause in force and the issue tracking it; solve that issue whatever its number, and when it closes the same command names the next. Where a defect you file while solving that issue stops it from closing, solve what you filed first and then return to the subclause. File and leave everything else: the open issues the command does not name are not this loop's work.` |
| :02 | `2,12,22,32,42,52 * * * *` | `REMINDER: ~/LRM.pdf is the source of truth.` |
| :03 | `3,13,23,33,43,53 * * * *` | `REMINDER: Solve the issue with a single commit and push.` |
| :04 | `4,14,24,34,44,54 * * * *` | `REMINDER: Solve the issue through parallel agents, without collisions.` |
| :05 | `5,15,25,35,45,55 * * * *` | `REMINDER: After pushing, deltahdl.yml might fail at integration tests. You can ignore that.` |
| :07 | `7,17,27,37,47,57 * * * *` | `REMINDER: Do not do anything but wait while a workflow is running.` |
| :09 | `9,19,29,39,49,59 * * * *` | `REMINDER: When you come up against a new problem, file a GitHub issue. A problem in the program — src/, lib/, scripts/, and the machinery under test/ — gets the sub-headers "Problem", "Why Unit Tests Did Not Catch It?", "Why Integration Tests Did Not Catch It?", "Why E2E Tests Did Not Catch It?", "Which Unit, Integration, or E2E regression tests would prevent this from happening again?", and "Proposed Solution". A problem in a workflow file, a linter configuration, a build file or the docs gets "Problem" and "Proposed Solution" only, and owes no tests.` |

### What to report

Then run the selector once and tell the user where the work stands.

Run `PYTHONPATH=.:scripts python3 -m next_subclause` and name the subclause and issue it printed. If the command reports there is nothing tracked, say so and do not start the reminders: there is nothing left to select, and every firing would report the same.

Say that seven reminders are running and give the two limits that come with them — the jobs live in this session only and are gone when it ends, and recurring jobs auto-expire after seven days.

Then start the first iteration in the same turn, without waiting for a reminder to arrive. Take the issue the selector just named and begin solving it under the seven prompts listed above. The one case that stops here is the case the report already names: a selector with nothing to take, where no jobs were created either.

## Stop

Call `CronList`, then call `CronDelete` once per job it returns — all of them, not only the seven this skill created. "Delete all your reminders" means the session ends with an empty schedule. Call `CronList` again afterwards to confirm it is empty, and report how many jobs were deleted.

`CronList` returning nothing is not a failure; say the schedule was already empty and stop.

## Notes

Cron jobs fire only while the session is idle, never mid-turn, because a turn cannot be preempted. That limit is the reason this skill does not try to correct drift in the middle of a task: what it can do is restart a loop that has stalled, which is the failure it is there to catch.

Starting the reminders starts the work, in the same turn. It used to end the turn instead and leave the first iteration to the first firing, which spent up to ten minutes on an idle session and needed nothing that was not in context already: this file lists all seven prompts, and invoking the skill is what reads them in. A reminder restarts a loop that has stalled, so until a first iteration has run there is no loop for one to restart.

The skill takes no issue number, and it used to. The number was a floor over the issues `next_subclause` cannot name, which left the caller deciding how much of the backlog came into scope on every invocation. The floor went rather than acquiring a fixed value, because a loop that selects one set is worth having and a loop whose set moves with an argument is not.

The one issue the loop takes beyond the subclause is bounded by that subclause and not by a number: a defect filed while solving it that stops it from closing. State such a bound by what the work in hand needs. A bound stated as a number selects issues by when they were filed, which says nothing about whether the subclause can close without them, and every wording of it read as an instruction to work the backlog.

The selector cannot reach the issues the work files for itself. `issue_title_for` in `lib/python/github/__init__.py` builds `Satisfy IEEE 1800-2023 §<subclause>`, and `next_subclause` looks issues up by that string alone, while those issues are titled by the defect they describe. So no run of the command will ever name one, whatever the campaign does next, and taking one is a person's decision rather than the loop's.

The first reminder names a command rather than an issue, and both halves of that matter. A cron prompt is fixed when the job is created while the work moves on without it, so a reminder naming the issue it started on would be wrong before the session ended and would say nothing about it. And an instruction to work through the open issues has only one way of being obeyed — read them all, then choose — which costs the whole backlog on every choice and grows with each issue the work files for itself. `next_subclause` answers instead from the dependency order, which cannot be wrong about what has to come first. What `next_subclause` matches on and why is in its own docstrings.

Reminder :04 names parallel agents because that is what solves an issue here, and the collision it rules out is two agents writing one file or two agents pushing where the run needs one push. It replaced two reminders that named a list of indivisible Claude tasks. Splitting one rule across two reminders bought nothing, and the list was never what did the work.

No reminder tells the loop to compact, because a session cannot compact itself. `/compact` is a built-in Claude Code command whose behaviour is coded into the CLI rather than a bundled skill handed to Claude, so the person at the keyboard is the only one who can run it, and the commands reference at <https://code.claude.com/docs/en/commands> names no tool, hook or flag that would let a session run it. What frees a long session's context instead is the auto-compact window at <https://code.claude.com/docs/en/model-config#set-the-auto-compact-window>, which Claude Code applies on its own as the conversation approaches the context limit. A `:06` reminder to compact before starting an issue was created and then removed for that reason: every firing of it asked for something no iteration of the loop could do, and spent a turn saying so.

Reminder :05 exists because `.github/workflows/deltahdl.yml` is red on every push and that is the standing state rather than a break. `scripts/run_sv_tests/__init__.py` ends in `sys.exit(min(failed, 1))`, so the `integration-test-coverage` job fails while any sv-test does, and 146 of 830 do. Issues #2910 through #2939 track those failures. Without the reminder, the standing instruction in `.claude/CLAUDE.md` to fix a red run in the session that finds it sends every iteration of the loop at the same 146 tests it was not started to fix.

The issue sub-headers in the last reminder are the user's wording, and reminder :09 is now the only place they are written down. Nothing else in the repository states them, so an issue is written from the reminder itself, `Proposed Solution` included.

That reminder carries the two-section form as well as the six, because it used to carry only the six and firing them alone every ten minutes was enough to produce the tests they asked for. A defect in a workflow file or a linter configuration was arriving beside a standing instruction to name the regression tests that would prevent it, and the instruction won: an issue over three copies of one yamllint rule set answered all four test sections and asked for two unit tests over a reading that would exist only because the rule set is written three times. A reminder that names only one case is read as though that case were the whole rule.
