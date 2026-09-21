---
name: reminders
description: Turn on or off seven standing reminders, one rule each, that fire once in every ten-minute period. Use when the user says "reminders on", "/reminders", or "reminders off". Takes "on" or "off"; no argument means "on".
---

# Reminders

## On

Call `CronList`. For each row below whose prompt is not already scheduled, call `CronCreate` with that `cron` and `prompt`, `recurring: true`. The offsets are staggered so the seven never fire together.

| Cron | Prompt |
| --- | --- |
| `1,11,21,31,41,51 * * * *` | `REMINDER: ~/IEEE 1800-2023.pdf is the source of truth. sv-tests was written against ~/IEEE 1800-2017.pdf, so its tags and file names carry 2017 clause numbers: read the 2017 edition only to learn what such a number meant there, resolve it to the 2023 clause, and let no 2017 number, wording or rule reach deltahdl's code, reports or tests.` |
| `3,13,23,33,43,53 * * * *` | `REMINDER: Work through a set of indivisible tasks, written down with TaskCreate before the work starts and marked with TaskUpdate as each one starts and finishes.` |
| `5,15,25,35,45,55 * * * *` | `REMINDER: Keep the task list itself current, not only the marks on it: a task that arises is added the moment it does, a task that turns out unneeded is removed, and a task whose shape changed is rewritten, so that the list always says what is left to do.` |
| `7,17,27,37,47,57 * * * *` | `REMINDER: Ensure every task on the list is indivisible, whether it was written with TaskCreate or rewritten with TaskUpdate.` |
| `9,19,29,39,49,59 * * * *` | `REMINDER: When you come up against a problem in this repo, solve it. Do not file a GitHub issue about it and move on — a problem you met is a problem you fix, in the same session, under the same standing rules as the issue you were working on.` |
| `0,10,20,30,40,50 * * * *` | `REMINDER: Work must be solved through a single commit & push.` |
| `6,16,26,36,46,56 * * * *` | `REMINDER: Do not do anything but wait while a workflow is running.` |

Report which were created and which were already running, then carry on with whatever the session was doing.

## Off

Call `CronList`, then `CronDelete` for each job whose prompt is one of the seven above and no other. Report how many were deleted.
