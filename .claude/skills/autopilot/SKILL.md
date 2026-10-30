---
name: autopilot
description: Start, restart or stop the standing reminders, with or without the loop that works through open issues. Use when the user says "start autopilot", "go autonomous on the subclauses", "go autonomous on issues above N", "go autonomous on the §5 issues", "go autonomous clause by clause", "reminders on", "reminders only", "stop autopilot", "reminders off", or asks to clear the reminders or to switch from one form to another ("restart autopilot", "switch to reminders only"). Takes "start bysubclause", "start byclause", "start byissuefloor <issue-number>", "start bylabel <label>", "start reminders-only", the same five forms after "restart", or "stop"; every "start" or "restart" form but "reminders-only" also takes `--skip-label <label>`, repeatable.
---

# Autopilot

## The six standing reminders

Every `start` form creates these.

| Cron | Prompt |
| --- | --- |
| `0,15,30,45 * * * *` | `REMINDER: Work through a set of tasks, written down with TaskCreate before the work starts and marked with TaskUpdate as each one starts and finishes.` |
| `2,17,32,47 * * * *` | `REMINDER: ~/IEEE 1800-2023.pdf is the source of truth. sv-tests was written against ~/IEEE 1800-2017.pdf, so its tags and file names carry 2017 clause numbers: read the 2017 edition only to learn what such a number meant there, resolve it to the 2023 clause, and let no 2017 number, wording or rule reach deltahdl's code, reports or tests. The UVM standard is ~/IEEE 1800.2-2020.pdf.` |
| `6,21,36,51 * * * *` | `REMINDER: Keep the task list itself current, not only the marks on it: a task that arises is added the moment it does, a task that turns out unneeded is removed, and a task whose shape changed is rewritten, so that the list always says what is left to do.` |
| `8,23,38,53 * * * *` | `REMINDER: A case of the rule an issue in hand documents is part of that issue's fix, never a new issue. Fix anything else you find on the spot when that is quicker and safer than filing it, and file the rest as issues: one per rule of a standard that deltahdl breaks or leaves untested, listing every case of it and labelled with both the standard it falls under (IEEE 1800-2023, IEEE 1800.2-2020 or IEEE 1735-2023) and its clause in that standard (§N or Annex X), creating the clause label first when the repository has none; or one per problem with deltahdl itself, such as a coverage gap, with neither label.` |
| `10,25,40,55 * * * *` | `REMINDER: Prune completed tasks off the Claude Code structured task list: set every task marked completed to the status deleted with TaskUpdate, so that the list holds only the tasks still open.` |
| `12,27,42,57 * * * *` | `REMINDER: Fix the rule, not the example. Before fixing an issue of a standard, list every case of the rule it documents: each form the rule allows and each form it forbids, written in every place the standard lets that form appear (a module, interface, program, checker, package, class, generate block, task or function, or the compilation unit, as applies) and with every kind of operand or type the rule names. Write a test for each case, one showing a forbidden form reported beside one showing the nearest allowed form accepted without a report, and make deltahdl pass every one of them in the same commit.` |

## The four loop reminders

Every `start` form but `reminders-only` adds these.

On `1,16,31,46 * * * *`, by form:

`start bysubclause`:

```text
REMINDER: Run gh issue list --state open --limit 10000 --json number,title --jq 'map(select(.title | test("^Satisfy IEEE 1800-2023 §([A-Z]|[0-9]+)(\\.[0-9]+)*$")) | .subclause = (.title | ltrimstr("Satisfy IEEE 1800-2023 §"))) | sort_by((.subclause | split(".") | map(tonumber? // .)), .number) | (first.subclause // "" | split(".") | first) as $c | map(select(.subclause | split(".") | first == $c)) | .[] | "§\(.subclause) #\(.number)"' for the lowest subclause with an open issue tracking it, followed by the other open subclauses of its clause, each with its issue's number. Solve the first of them whatever its number, taking any of the rest alongside it where that makes sense, and commit and push each piece of work once it stands on its own; when they close, the same command names the next. The open issues the command does not name are not this loop's work.
```

`start byclause`:

```text
REMINDER: Run gh issue list --state open --limit 10000 --json number,title,labels --jq 'map({number, title, labels: [.labels[].name]}) as $all | first(("IEEE 1800-2023", "IEEE 1800.2-2020", "IEEE 1735-2023") as $s | ($all | map(select(.labels | index([$s])))) as $std | ($std | map(.labels[] | select(test("^§[0-9]+$")) | ltrimstr("§") | tonumber) | min | if . then "§\(.)" else null end) as $c | ($std | map(.labels[] | select(test("^Annex [A-Z]$"))) | min) as $a | ($c // $a) as $l | select($l) | {standard: $s, label: $l, issues: ($std | map(select(.labels | index([$l]))))}) // null' for the open issues of the first standard, in the order IEEE 1800-2023, IEEE 1800.2-2020, IEEE 1735-2023, whose issues carry a clause label, and of the lowest numbered clause that labels one of them, or, when none carries the label of a numbered clause, of the first annex in letter order that labels one; work every Reconcile issue in the list first, as the autopilot skill's section on Reconcile issues says, then solve the rest test first, taking related issues together where that makes sense and committing and pushing each piece of work once it stands on its own, and run the same command again when they close. The open issues the command does not list are not this loop's work.
```

`start byissuefloor <issue-number>`:

```text
REMINDER: Run gh issue list --state open --limit 10000 --json number,title,labels --jq 'map(select(.number > {X}) | {number, title, labels: [.labels[].name]})' for the open issues above #{X}; work every Reconcile issue in the list first, as the autopilot skill's section on Reconcile issues says, then solve the rest test first, taking related issues together where that makes sense and committing and pushing each piece of work once it stands on its own, and run the same command again when they close. The issues at or below #{X} are a person's to take rather than this loop's.
```

`start bylabel <label>`:

```text
REMINDER: Run gh issue list --state open --label '{L}' --limit 10000 --json number,title,labels --jq 'map({number, title, labels: [.labels[].name]})' for the open issues labelled '{L}'; work every Reconcile issue in the list first, as the autopilot skill's section on Reconcile issues says, then solve the rest test first, taking related issues together where that makes sense and committing and pushing each piece of work once it stands on its own, and run the same command again when they close. The open issues without the label '{L}' are not this loop's work.
```

And these:

| Cron | Prompt |
| --- | --- |
| `4,19,34,49 * * * *` | `REMINDER: Continue autonomously, unless you need human feedback about ANYTHING — not just about what to take next. When you do, rewrite the issue's title if necessary, rewrite the issue's body, label the issue 'needs decision', and move on to the next issue.` |
| `5,20,35,50 * * * *` | `REMINDER: Before working on an issue, ensure the issue is up to date. If it is outdated, rewrite its title and body as necessary, delete all its comments, and ensure its labels are correct: the label of the standard it falls under and the label of its clause in that standard. Ensure too that it documents a single rule of a standard, or a single problem with deltahdl itself: if it documents more than one, split it into one issue per rule or problem, reusing the issue itself as one of those splits; if other open issues document cases of the same rule, fold their cases into it and close them as duplicates of it.` |
| `11,26,41,56 * * * *` | `REMINDER: Before labeling an issue with 'needs decision', assess the issue against the sources of truth to determine whether it truly needs a decision.` |

## Start

`start` alone is `bysubclause`, `start <issue-number>` is `byissuefloor`, and `start §5` is `bylabel`.

Any form but `reminders-only` may be followed by `--skip-label <label>`, once per label, quoted when it holds a space. Each puts `map(select(all(.labels[]; .name != "<label>"))) |` and a space at the very start of the loop command's `--jq` program, adding `labels` to its `--json` fields where they are missing (the `bysubclause` form), and appends to that reminder, after a space, `An issue labelled '<label>' is left to a person, whatever else it carries.` Two labels give `map(select(all(.labels[]; .name != "needs decision"))) | map(select(all(.labels[]; .name != "blocked"))) |` and a space before the program. The label is never left out through a `--search` term: GitHub's search returns at most 1000 issues, so a search listing drops every open issue older than the newest 1000, where `--limit 10000` without one pages through them all.

For any form but `reminders-only`, run the loop's `gh issue list` command once; if it names no issue, create the six standing reminders only.

Call `CronList`. A job on one of the form's cron slots whose prompt differs from that slot's reminder is a stale version of it: `CronDelete` it. Then `CronCreate` with `recurring: true` each reminder of the form whose prompt is not already scheduled, substituting the number for `{X}` or the label for `{L}`. Then begin solving the command's first issue.

## Restart

`restart` takes the forms `start` takes, with the same shorthands and the same `--skip-label` flags, and leaves scheduled exactly the reminders of the form it names, whatever was scheduled before.

For any form but `reminders-only`, run the loop's `gh issue list` command once; if it names no issue, the form's reminders are the six standing reminders only.

Call `CronList`. `CronDelete` every job that is not one of the form's reminders: a job on a slot the form does not use, a job whose prompt differs from its slot's reminder, and every job but one on a slot that holds more than one. Then `CronCreate` with `recurring: true` each reminder of the form whose prompt is not scheduled after those deletions, substituting the number for `{X}` or the label for `{L}`. Then, for any form but `reminders-only`, begin solving the command's first issue.

## Reconcile issues

An issue titled `Reconcile deltahdl against <section> of IEEE 1800-2023 (<title>)` stands for one section of the standard's table of contents, read to two levels. Its body defines rules and cases and says what reconciling the section means: every rule the section states is listed with every case of it, and each case is shown by a test under `test/` that asserts the standard's outcome, or held by the open issue of its rule until a test does. A loop works every open Reconcile issue of a clause before any other issue of that clause, since the reading files the clause's issues and rewrites the ones already open. A Reconcile issue is worked by reading and filing, and it closes without a commit.

The clause's open Reconcile issues are worked one at a time, in section order. Each step below is a task written with TaskCreate before it starts and marked with TaskUpdate as it starts and finishes:

1. **List.** Read the section the issue names, every page of it, one page per Read call, and list every rule it states and every case of each. A rule is a requirement the text states: a syntax production or a restriction on it, a "shall" or "shall not", a result a tool could get observably wrong (a value, type, width, order, elaboration outcome, or VPI object, relation or property), a required error report, or a permission a tool must accept. A rule the section only refers to belongs to the clause or annex that states it, and each case of it is marked with that clause. A case is one form the rule allows or forbids, with the nearest allowed form beside each forbidden one, in each place it can be written where its handling could differ, with each kind of operand or type the rule names where the outcome could differ, and in each way of naming the construct where that matters. Write the list to `<scratchpad>/reconcile/N_rules.md`, `<scratchpad>` being the session's scratchpad directory and `N` the issue's number, so that the list outlives the context it was read in.
2. **Find.** For each case, search the whole of `test/` for the test that shows it, by the construct's source text, its diagnostic's words and its subclause, and open the test to see that it exercises that exact case and asserts the outcome the standard gives. Record the test beside the case, or record none, and note a test that asserts an outcome the standard does not give.
3. **File.** For each rule with a case that names no test, or a test asserting a wrong outcome, do step 4 of the Reconcile issue's body, filing a case that belongs to another clause or annex on the issue of its rule there: find the rule's issue, open or closed, and reopen and rewrite it, or file one, listing every case, ticked with its test or unticked, labelled exactly `IEEE 1800-2023` and the rule's own clause label, with every other clause label removed and its comments deleted.
4. **Record.** Add the `## Rules` section of step 5 to the Reconcile issue's body through a guarded rewrite, per `.claude/memories/guarding-an-issue-body-rewrite.md`. A rule names its tests only when every case of it names one, and otherwise names its issue.
5. **Close** the Reconcile issue.

Then the clause's other issues are taken, as below.

## Other issues

A Reconcile issue is never solved alongside other issues. Each other issue is fixed for every case of its rule, per `.claude/memories/fixing-a-rule-in-full.md`, not only for the example it gives, and test first: each case's test is written before the code that makes it pass. Related issues may be solved together. Each piece of work is committed and pushed once it stands on its own, with one `Closes #N` line per issue it solves.

## Stop

Call `CronList`, then `CronDelete` for every job it returns.
