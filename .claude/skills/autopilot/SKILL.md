---
name: autopilot
description: Start or stop the standing reminders that keep an autonomous issue-solving session on the rails. Use when the user says "start autopilot", "go autonomous on the subclauses", "go autonomous on issues above N", "go autonomous on the §5 issues", "stop autopilot", or asks to clear the reminders. Takes "start bysubclause", "start byissuefloor <issue-number>", "start bylabel <label>" or "stop".
---

# Autopilot

Seven recurring reminders, one per standing rule, that fire back into this session while it works through open issues on its own. Each rule gets its own reminder and carries that rule alone, so that no rule can be quietly dropped from a merged block of text and no reminder restates another's, and the fire times are staggered across the ten-minute period so they arrive one at a time rather than as a wall.

The argument selects the mode: `start bysubclause`, `start byissuefloor <issue-number>`, `start bylabel <label>`, or `stop`.

## Start

Three forms select the work, and they differ in one reminder. `start bysubclause` takes the lowest subclause that still has an open issue tracking it. `start byissuefloor <issue-number>` takes the open issues above the number, which are what this work has filed for itself and which the subclause resolver cannot name at all. `start bylabel <label>` takes the open issues carrying the label, such as `§5` for the issues filed against clause 5.

Create seven jobs with `CronCreate`, exactly as listed below. Use `recurring: true` (the default). Take `:01` from the form the user asked for, substituting the number they gave for `{X}` or the label they gave for `{L}` where the form carries one, and leave the other six verbatim. Each `cron` field is a distinct offset within the same ten-minute period, so the seven reminders never land together.

### The reminder that selects the work

`start bysubclause` takes the issue its pipeline names: the lowest subclause among the open issues titled `Satisfy IEEE 1800-2023 §<subclause>`, and that issue's number. What it leaves is the rest of the tracker: the open issues the command does not name are somebody else's finding rather than this loop's. Matching is on the canonical title, so those issues are outside this form by construction.

`start byissuefloor <issue-number>` runs no resolver. It works the open issues above the number, and it says nothing about which of them comes first. Nothing records an order over these issues, so the loop takes one and takes another when it closes.

`start bylabel <label>` runs no resolver either. It works the open issues carrying the label, exactly as the user wrote it — `gh label list` prints the repository's labels, and the clause labels are `§1` through `§41`, `Annex A` and `Annex B` — and, like the floor form, it says nothing about which of them comes first. A label with a space in it, `Annex A`, stands inside the single quotes the command already has.

The number belongs to `byissuefloor` alone. A floor applied to the subclause form would rule out every subclause there is to take, because the issue tracking a subclause was opened when the subclause was catalogued rather than when the campaign reached it, so it sits below anything the work has filed since. The label belongs to `bylabel` alone by the same reading: the `Satisfy` issues carry no clause label that the subclause form could use, and a floor and a label together would select two sets where a loop is worth having for one.

Where the user named no form, what they did give still says which one. `start` alone and `start subclauses` are `bysubclause`, because a form carrying no number cannot be the one whose whole argument is a number, `start <issue-number>` is `byissuefloor` by the same reading run backwards, and `start §5` is `bylabel`, because a number with a section sign in front of it is not an issue number and is a label the repository has. `start byissuefloor` with no number and `start bylabel` with no label are the two invocations that are missing something: ask for the number or the label before creating anything.

All three forms fire `:01` on `1,11,21,31,41,51 * * * *`. The prompt is the whole of the difference, and it goes below in a code block rather than a table cell because the `byissuefloor` command contains the character a table row uses to end a cell.

`start bysubclause`:

```text
REMINDER: Run gh issue list --state open --limit 1000 --json number,title --jq 'map(select(.title | test("^Satisfy IEEE 1800-2023 §([A-Z]|[0-9]+)(\\.[0-9]+)*$")) | .subclause = (.title | ltrimstr("Satisfy IEEE 1800-2023 §"))) | sort_by((.subclause | split(".") | map(tonumber? // .)), .number) | first // empty | "§\(.subclause) #\(.number)"' for the lowest subclause with an open issue tracking it and that issue's number; solve that issue whatever its number, and when it closes the same command names the next. The open issues the command does not name are not this loop's work.
```

`start byissuefloor <issue-number>`, with the number the user gave substituted for `{X}` in all three places:

```text
REMINDER: Run gh issue list --state open --limit 1000 --json number,title --jq 'map(select(.number > {X}))' for the open issues above #{X}; take one, solve it, and run the same command again when it closes. The issues at or below #{X} are a person's to take rather than this loop's.
```

`start bylabel <label>`, with the label the user gave substituted for `{L}` in all three places:

```text
REMINDER: Run gh issue list --state open --label '{L}' --limit 1000 --json number,title for the open issues labelled '{L}'; take one, solve it, and run the same command again when it closes. The open issues without the label '{L}' are not this loop's work.
```

### The six reminders both forms carry

| Offset | Cron | Prompt |
| --- | --- | --- |
| :02 | `2,12,22,32,42,52 * * * *` | `REMINDER: ~/LRM.pdf is the source of truth.` |
| :03 | `3,13,23,33,43,53 * * * *` | `REMINDER: Solve the issue with a single commit and push.` |
| :04 | `4,14,24,34,44,54 * * * *` | `REMINDER: Continue autonomously, unless you need human feedback about ANYTHING — not just about what to take next.` |
| :05 | `5,15,25,35,45,55 * * * *` | `REMINDER: After pushing, deltahdl.yml might fail at its integration or e2e tests. You can ignore that.` |
| :07 | `7,17,27,37,47,57 * * * *` | `REMINDER: Do not do anything but wait while a workflow is running.` |
| :08 | `8,18,28,38,48,58 * * * *` | `REMINDER: Solve what you find rather than filing it and moving on. A failing integration or e2e test in deltahdl.yml is the exception: leave that one where it is.` |

### What to report

Then run the form's own selector once and tell the user where the work stands.

For `start bysubclause`, run the `gh issue list` pipeline from that form's prompt and name the subclause and issue it printed.

For `start byissuefloor <issue-number>`, run the `gh issue list` command from that form's prompt and name the floor it was given, how many open issues stand above it, and which of them the first iteration will take.

For `start bylabel <label>`, run the `gh issue list` command from that form's prompt and name the label it was given, how many open issues carry it, and which of them the first iteration will take.

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

`start bysubclause` is bounded by where a finding came from rather than by a number. What the loop turns up while solving the subclause it solves; what it did not turn up, the tracker's standing backlog, it leaves. Bounding it that way is what keeps the form from reading as an instruction to work the backlog, since a number would select issues by when they were filed, which says nothing about whether this loop is what found them. Where the caller does want the backlog worked, `start byissuefloor` is the form that says so, and it says it instead of the subclause rather than alongside it — a loop is worth having where it selects one set, and two forms are worth having where each names its own.

`start bylabel` exists because the floor selects by when an issue was filed and the subclause form by a title only the `Satisfy` issues carry, and neither can name the issues filed against one clause. Those are titled by the defect they describe, `Clause 5: ...`, and were filed over a span of numbers that other clauses' issues share, so no floor bounds them and no title pattern the subclause pipeline could be given picks them out; the clause label is the one thing they carry that says which clause they belong to. The label is taken as an argument rather than read from anywhere, for the reason the floor is: which clause is worth working on the day is the caller's judgement. It is as weak a handle as the floor — a set with no order over it — and the prompt says `take one` for the same reason the floor's does. Only the label filter is in the prompt, with no `jq` stage, because `gh issue list --label` already answers the question and a filter written twice would be one more place for the rule to drift from.

`start byissuefloor` exists because the subclause selector cannot reach the issues the work files for itself. The pipeline keeps only the titles of the form `Satisfy IEEE 1800-2023 §<subclause>`, while those issues are titled by the defect they describe. So no run of the command will ever name one, whatever the campaign does next, and an issue number is the only handle the skill has on them. That set stops growing under reminder :08, which has the loop solve a finding instead of writing it into the tracker, but the issues filed before it does not go anywhere and the floor is still what reaches them. It is a weaker handle than the one the subclauses get: the subclause pipeline answers with an order, the standard's own numbering, while a floor says only which issues are in scope.

The rule about whether to stop is a reminder of its own rather than the first sentence of the selector. It is not a rule about what to take, and it reads the same whichever form was asked for, so written into the two `:01` prompts it was the one thing this file said twice: an edit to one form's wording and not the other left the rule the session was running under depending on which form had been invoked. What stayed behind in `:01` is the selector and the two boundaries that are stated in its terms, because neither of those stands alone on arrival — one names no subclause and the other no set for everything else to exclude, so either firing by itself would be a sentence about a selector that is not in the message.

The first reminder of either form names a command rather than an issue, and both halves of that matter. A cron prompt is fixed when the job is created while the work moves on without it, so a reminder naming the issue it started on would be wrong before the session ended and would say nothing about it. And an instruction to work through the open issues has only one way of being obeyed — read them all, then choose — which costs the whole backlog on every choice and grows with each issue the work files for itself. Both prompts name a query instead: the subclause pipeline answers from the numbering the open issues already carry in their titles, which the tracker keeps current without anything in this repository being kept in step with it, and the `gh issue list` filter answers from the floor, which is what keeps the listing from being the whole backlog. Where the subclause form gets an order out of that, the floor form gets a set and chooses within it.

The subclause selector is a pipeline written into the reminder rather than a script the reminder runs. Each stage is one program doing one thing: `gh` lists the open issues as JSON, and `jq` keeps the canonical titles, splits each subclause on `.` into numbers, with an annex letter staying a string that jq sorts after every number, orders by that key and then by issue number, and prints the first as `§<subclause> #<number>`. Composing them in the reminder means the rule the reminder carries is readable in the reminder itself, and there is no second place for it to drift from. `scripts/next_subclause` was the script this form ran until 2026-09-14, and it answered from `docs/dependency_graph.json`, a recorded dependency order; when the clause 16 and 18 issues were reopened because a since-decommissioned script had solved them in place of this skill, that order named `§16.9` ahead of `§16.1`, and the lowest open subclause is what the loop takes. The pipeline prints nothing when no `Satisfy` issue is open, which is the selector naming nothing.

A sentence in `:01` saying to solve a defect that stops the issue from closing before returning to the subclause was removed on the same day, because it is reminder :08's rule stated a second time: :08 says to solve what the loop finds rather than filing it, and a defect that blocks the issue in hand is what the loop finds. Each reminder carries one rule so that an edit to the rule lands in one place; what `:01` keeps is the selector and the boundary that is stated in the selector's terms.

No reminder tells the loop to compact, because a session cannot compact itself. `/compact` is a built-in Claude Code command whose behaviour is coded into the CLI rather than a bundled skill handed to Claude, so the person at the keyboard is the only one who can run it, and the commands reference at <https://code.claude.com/docs/en/commands> names no tool, hook or flag that would let a session run it. What frees a long session's context instead is the auto-compact window at <https://code.claude.com/docs/en/model-config#set-the-auto-compact-window>, which Claude Code applies on its own as the conversation approaches the context limit. A `:06` reminder to compact before starting an issue was created and then removed for that reason: every firing of it asked for something no iteration of the loop could do, and spent a turn saying so.

Reminder :05 exists because `.github/workflows/deltahdl.yml` is red on every push and that is the standing state rather than a break. `scripts/run_sv_tests/__init__.py` ends in `sys.exit(min(failed, 1))`, so the `integration-test-coverage` job fails while any sv-test does, and 146 of 830 do. Issues #2910 through #2939 track those failures. Without the reminder, the standing instruction in `.claude/memories/fixing-a-red-run.md` to fix a red run in the session that finds it sends every iteration of the loop at the same 146 tests it was not started to fix.

Reminder :05 names both job families because reminder :08 draws its exception around both, and drawing it at one job would leave the other unstated the first time it went red. Today the standing failure is `integration-test-coverage` alone: `e2e-test-coverage` runs `run_sim_tests` and passes on the same runs the sv-tests job fails on.

Reminder :08 is why nothing else waits. A defect the loop finds is fixed in the commit in hand rather than written into the tracker for a later iteration to take, which is what `.claude/memories/what-does-not-get-filed.md` already says of a defect the commit in hand fixes: solving a finding is not a rule traded away for this one, it is the case that memory carves out. The exception is the integration and e2e tests, and it is the same exception :05 states about the run: a loop sent at those tests spends every iteration on the 146 it was not started to fix.

A `:09` reminder saying to solve a new problem when the loop came up against one was removed when :08 was written, because it had stopped saying anything :08 does not. A defect the loop finds is a new problem, and :09 set no scope that held any back, so the two prompts asked for the same thing on arrival — with :08 the stronger of them, since it names what deferring would have looked like and carries the one exception. What remains of :09 that :08 does not state is covered by :04, which is the reminder that says not to hand the work back.
