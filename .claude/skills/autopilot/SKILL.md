---
name: autopilot
description: Start or stop the standing reminders that keep an autonomous issue-solving session on the rails. Use when the user says "start autopilot", "go autonomous on issues above N", "stop autopilot", or asks to clear the reminders. Takes "start <issue-number>" or "stop".
---

# Autopilot

Seven recurring reminders, one per standing rule, that fire back into this session while it works through open issues on its own. Each rule gets its own reminder so that no rule can be quietly dropped from a merged block of text, and the fire times are staggered across the ten-minute period so they arrive one at a time rather than as a wall.

The argument selects the mode: `start <issue-number>` or `stop`.

## Start

The issue number is required — it is the `{X}` in the first reminder. If the user did not give one, ask for it before creating anything.

Create seven jobs with `CronCreate`, exactly as listed below. Use `recurring: true` (the default). Substitute the issue number for `{X}` in the first prompt and leave the other six verbatim. Each `cron` field is a distinct offset within the same ten-minute period, so the seven reminders never land together:

| Offset | Cron | Prompt |
| --- | --- | --- |
| :01 | `1,11,21,31,41,51 * * * *` | `REMINDER: Continue autonomously, unless you need human feedback about ANYTHING — not just about what to take next. Run PYTHONPATH=.:scripts python3 -m next_subclause for the subclause in force and the issue tracking it; solve that issue, and when it closes the same command names the next. Issues above #{X} are in scope alongside it, and are the ones this work has filed for itself. Issues at or below #{X} are not.` |
| :02 | `2,12,22,32,42,52 * * * *` | `REMINDER: ~/LRM.pdf is the source of truth.` |
| :03 | `3,13,23,33,43,53 * * * *` | `REMINDER: Issues must be solved in single pushes.` |
| :04 | `4,14,24,34,44,54 * * * *` | `REMINDER: Issues must be solved through a set of indivisible Claude tasks.` |
| :06 | `6,16,26,36,46,56 * * * *` | `REMINDER: Ensure Claude tasks are indivisible.` |
| :07 | `7,17,27,37,47,57 * * * *` | `REMINDER: Do not do anything but wait while a workflow is running.` |
| :09 | `9,19,29,39,49,59 * * * *` | `REMINDER: When you come up against a new problem, file a GitHub issue with the sub-headers "Problem", "Why Unit Tests Did Not Catch It?", "Why Integration Tests Did Not Catch It?", "Why E2E Tests Did Not Catch It?", "Which Unit, Integration, or E2E regression tests would prevent this from happening again?", and "Proposed Solution".` |

Then run `next_subclause` once and tell the user where the campaign stands: the subclause and issue it named, which issue number is the floor, that seven reminders are running, and the two limits that come with them — the jobs live in this session only and are gone when it ends, and recurring jobs auto-expire after seven days. If the command reports there is nothing tracked, say so; the reminders are still worth starting, because the floor still selects work.

Do not begin working the issues as part of starting the reminders. Starting autopilot and doing the work are separate; the first reminder will arrive within ten minutes and start the loop, unless the user asks to begin straight away.

## Stop

Call `CronList`, then call `CronDelete` once per job it returns — all of them, not only the seven this skill created. "Delete all your reminders" means the session ends with an empty schedule. Call `CronList` again afterwards to confirm it is empty, and report how many jobs were deleted.

`CronList` returning nothing is not a failure; say the schedule was already empty and stop.

## Notes

Cron jobs fire only while the session is idle, never mid-turn, because a turn cannot be preempted. That limit is the reason this skill does not try to correct drift in the middle of a task: what it can do is restart a loop that has stalled, which is the failure it is there to catch.

The first reminder names a command rather than a subclause, and both halves of that matter. A cron prompt is fixed when the job is created while the campaign moves on without it, so a reminder naming the subclause it started on would be wrong before the session ended and would say nothing about it. And an instruction to work through the open issues has only one way of being obeyed — read them all, then choose — which costs the whole backlog on every choice and grows with each issue the work files for itself. `next_subclause` answers instead from the recorded dependency order, which cannot be wrong about what has to come first: a subclause whose dependencies are unmet is not available whatever its issue says. What that command matches on and why is in its own docstrings.

The issue sub-headers in the last reminder are the user's wording. `CLAUDE.md` carries the same six sections, the regression one included, and `docs/claude/how-issues-are-written.md` is the authority when an issue is actually being written. All three name the sections identically, `Proposed Solution` included.
