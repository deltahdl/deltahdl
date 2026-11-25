---
name: autopilot
description: Start, restart or stop the standing reminders, with or without the loop that works through open issues. Use when the user says "start autopilot", "go autonomous on the subclauses", "go autonomous on issues above N", "go autonomous on the §5 issues", "go autonomous clause by clause", "reminders on", "reminders only", "stop autopilot", "reminders off", or asks to clear the reminders or to switch from one form to another ("restart autopilot", "switch to reminders only"). Takes "start bysubclause", "start byclause", "start byissuefloor <issue-number>", "start bylabel <label>", "start reminders-only", the same five forms after "restart", or "stop"; every "start" or "restart" form but "reminders-only" also takes `--skip-label <label>`, repeatable.
---

# Autopilot

Every form's work, reading, searching and filing as well as code, is done in the session itself: no Agent or Workflow call takes any part of it, as the `permissions.deny` entries for both tools in `.claude/settings.json` enforce.

## Reminders

Each reminder states one indivisible matter and fires every 15 minutes, per `.claude/memories/a-reminder-states-one-matter.md`. Two reminders can share a minute, so a scheduled job is told apart from another by its prompt.

What the user instructs is done in full and at once, whatever a reminder says, per `.claude/memories/what-the-user-instructs-is-done.md`.

## The standing reminders

Every `start` form creates these.

| Cron | Prompt |
| --- | --- |
| `1,16,31,46 * * * *` | `REMINDER: ~/IEEE 1800-2023.pdf is the source of truth for SystemVerilog.` |
| `2,17,32,47 * * * *` | `REMINDER: sv-tests was written against ~/IEEE 1800-2017.pdf, so its tags and file names carry 2017 clause numbers: read the 2017 edition only to learn what such a number meant there, resolve it to the 2023 clause, and let no 2017 number, wording or rule reach deltahdl's code, reports or tests.` |
| `3,18,33,48 * * * *` | `REMINDER: ~/IEEE 1800.2-2020.pdf is the source of truth for UVM.` |
| `4,19,34,49 * * * *` | `REMINDER: Every section of ~/IEEE 1800-2023.pdf has been swept and a test written for each case of each rule it states: a plain name passes, and DISABLED_ marks what deltahdl does not yet do, so take a case's test to be under test/ already.` |
| `5,20,35,50 * * * *` | `REMINDER: Before proposing or adding a test, search all of test/ for one that already shows the case, open it, trace the code it runs, and add yours once you can name what it would catch that the existing one would not.` |
| `6,21,36,51 * * * *` | `REMINDER: Before deleting or weakening a test, establish what it asserts, what the standard requires and which remaining test shows each of its correct cases, and say so in the commit that removes it.` |
| `7,22,37,52 * * * *` | `REMINDER: While anything runs in the background, whether a CI run, a build, a test run, the pre-push check or any other command, only wait until its notification arrives, except for what the user instructs, which is done in full at once.` |
| `8,23,38,53 * * * *` | `REMINDER: Start a background command as the last call of a turn.` |
| `9,24,39,54 * * * *` | `REMINDER: A case of the rule an issue in hand documents is part of that issue's fix, never a new issue.` |
| `10,25,40,55 * * * *` | `REMINDER: Fix a defect outside the rule in hand on the spot when that is quicker and safer than filing it, and file it otherwise.` |
| `11,26,41,56 * * * *` | `REMINDER: File one issue per rule of a standard that deltahdl breaks or leaves untested, listing every case of it, or one per problem with deltahdl itself, such as a coverage gap.` |
| `12,27,42,57 * * * *` | `REMINDER: Label an issue of a standard with both the standard it falls under (IEEE 1800-2023, IEEE 1800.2-2020 or IEEE 1735-2023) and its clause in that standard (§N or Annex X), creating the clause label first when the repository has none; an issue about deltahdl itself takes neither.` |
| `13,28,43,58 * * * *` | `REMINDER: Build and run each case's test before writing its fix, and read why it fails: it fails for the reason its issue names, or it has found another defect, which is fixed on the spot or filed before the fix is designed.` |
| `14,29,44,59 * * * *` | `REMINDER: Before every push, commit, then run .claude/skills/pre-push-checks/check.sh in the background over the touched test files, naming at most the targets that hold the existing tests of the rule in hand; push once it prints that every check passed, or reports only a changed line that a test file it did not run reaches.` |
| `1,16,31,46 * * * *` | `REMINDER: Leave to CI every unit test beyond the rule in hand and the touched files, clang-tidy beyond the touched files, and the integration and e2e runs.` |
| `2,17,32,47 * * * *` | `REMINDER: Keep the task list current with TaskCreate and TaskUpdate: add a task when it arises, mark each one as it starts and finishes, rewrite or remove one whose shape changed or that turned out unneeded, and delete finished ones, so the list says what is left to do.` |
| `3,18,33,48 * * * *` | `REMINDER: Before fixing an issue of a standard, list every case of the rule it documents: each form the rule allows and each form it forbids, written in every place the standard lets that form appear (a module, interface, program, checker, package, class, generate block, task or function, or the compilation unit, as applies) and with every kind of operand or type the rule names.` |
| `4,19,34,49 * * * *` | `REMINDER: Make deltahdl pass the test of every case of the rule in the same commit, with the test showing a forbidden form reported beside one showing the nearest allowed form accepted without a report.` |

## The loop reminders

Every `start` form but `reminders-only` adds these.

The loop command is on `5,20,35,50 * * * *`, by form:

`start bysubclause`:

```text
REMINDER: Run gh issue list --state open --limit 10000 --json number,title --jq 'map(select(.title | test("^Satisfy IEEE 1800-2023 §([A-Z]|[0-9]+)(\\.[0-9]+)*$")) | .subclause = (.title | ltrimstr("Satisfy IEEE 1800-2023 §"))) | sort_by((.subclause | split(".") | map(tonumber? // .)), .number) | (first.subclause // "" | split(".") | first) as $c | map(select(.subclause | split(".") | first == $c)) | .[] | "§\(.subclause) #\(.number)"' for the lowest subclause with an open issue tracking it, followed by the other open subclauses of its clause, each with its issue's number. Read the issue of every subclause it names and work the group that holds the first of them; when it closes, the same command names the next. The open issues the command does not name are not this loop's work.
```

`start byclause`:

```text
REMINDER: Run gh issue list --state open --limit 10000 --json number,title,labels --jq 'map({number, title, labels: [.labels[].name]}) as $all | ($all | map(select(.labels == []))) as $bare | if ($bare | length) > 0 then {label: null, issues: $bare} else first(("IEEE 1800-2023", "IEEE 1800.2-2020", "IEEE 1735-2023") as $s | ($all | map(select(.labels | index([$s])))) as $std | ($std | map(.labels[] | select(test("^§[0-9]+$")) | ltrimstr("§") | tonumber) | min | if . then "§\(.)" else null end) as $c | ($std | map(.labels[] | select(test("^Annex [A-Z]$"))) | min) as $a | ($c // $a) as $l | select($l) | {standard: $s, label: $l, issues: ($std | map(select(.labels | index([$l]))))}) // null end' for the open issues that carry no label at all while any does, and otherwise for the open issues of the first standard, in the order IEEE 1800-2023, IEEE 1800.2-2020, IEEE 1735-2023, whose issues carry a clause label, and of the lowest numbered clause that labels one of them, or, when none carries the label of a numbered clause, of the first annex in letter order that labels one; work every Reconcile issue in the list first, as the autopilot skill's section on Reconcile issues says, then the rest, a group at a time, and run the same command again when a group closes. The open issues the command does not list are not this loop's work.
```

`start byissuefloor <issue-number>`:

```text
REMINDER: Run gh issue list --state open --limit 10000 --json number,title,labels --jq 'map(select(.number > {X}) | {number, title, labels: [.labels[].name]}) | sort_by((if .labels == [] then 0 elif any(.labels[]; test("^(§[0-9]+|Annex [A-Z])$")) then 1 else 2 end), ([.labels[] | select(test("^§[0-9]+$")) | ltrimstr("§") | tonumber] | min // 1000), ([.labels[] | select(test("^Annex [A-Z]$"))] | min // ""), (.title | startswith("Reconcile ") | not), .number)' for the open issues above #{X}, those carrying no label first, then those carrying a clause label, by lowest numbered clause and then annex letter, each clause's Reconcile issues ahead of its others, then the rest; work them in that order, each Reconcile issue as the autopilot skill's section on Reconcile issues says, and the others a group at a time, and run the same command again when a group closes. The issues at or below #{X} are a person's to take rather than this loop's.
```

`start bylabel <label>`:

```text
REMINDER: Run gh issue list --state open --label '{L}' --limit 10000 --json number,title,labels --jq 'map({number, title, labels: [.labels[].name]}) | sort_by((if .labels == ["{L}"] then 0 elif any(.labels[]; test("^(§[0-9]+|Annex [A-Z])$")) then 1 else 2 end), ([.labels[] | select(test("^§[0-9]+$")) | ltrimstr("§") | tonumber] | min // 1000), ([.labels[] | select(test("^Annex [A-Z]$"))] | min // ""), (.title | startswith("Reconcile ") | not), .number)' for the open issues labelled '{L}', those carrying no other label first, then those carrying a clause label, by lowest numbered clause and then annex letter, each clause's Reconcile issues ahead of its others, then the rest; work them in that order, each Reconcile issue as the autopilot skill's section on Reconcile issues says, and the others a group at a time, and run the same command again when a group closes. The open issues without the label '{L}' are not this loop's work.
```

And these:

| Cron | Prompt |
| --- | --- |
| `6,21,36,51 * * * *` | `REMINDER: Before solving an issue the loop's command lists, read the title of every issue in the list and the body of each that shares a subclause or names the same code as another, and sort them into groups of issues whose fixes go through the same code.` |
| `7,22,37,52 * * * *` | `REMINDER: Take the first group whole as one piece of work, adding to it any other listed issues you choose.` |
| `8,23,38,53 * * * *` | `REMINDER: Commit and push each commit once it closes at least one issue, as many as you choose to finish in it, with every case of each one's rule passing.` |
| `9,24,39,54 * * * *` | `REMINDER: Before writing any of its code, split by rule an issue whose open cases cannot all land in one commit.` |
| `10,25,40,55 * * * *` | `REMINDER: Continue autonomously, unless you need human feedback about ANYTHING, not just about what to take next.` |
| `11,26,41,56 * * * *` | `REMINDER: When an issue needs human feedback, rewrite its title if necessary and its body, label it 'needs decision', and move on to the next issue.` |
| `12,27,42,57 * * * *` | `REMINDER: Before working on an issue, check that it is up to date, and correct its title, body and labels where it is not.` |
| `13,28,43,58 * * * *` | `REMINDER: Split an issue that turns out to hold more than one rule or problem, and merge one that repeats another open issue, where that helps the work.` |
| `14,29,44,59 * * * *` | `REMINDER: Before labeling an issue with 'needs decision', assess the issue against the sources of truth to determine whether it truly needs a decision.` |

## Start

`start` alone is `bysubclause`, `start <issue-number>` is `byissuefloor`, and `start §5` is `bylabel`.

Any form but `reminders-only` may be followed by `--skip-label <label>`, once per label, quoted when it holds a space. Each puts `map(select(all(.labels[]; .name != "<label>"))) |` and a space at the very start of the loop command's `--jq` program, adding `labels` to its `--json` fields where they are missing (the `bysubclause` form), and appends to that reminder, after a space, `An issue labelled '<label>' is left to a person, whatever else it carries.` Two labels give `map(select(all(.labels[]; .name != "needs decision"))) | map(select(all(.labels[]; .name != "blocked"))) |` and a space before the program. The label is never left out through a `--search` term: GitHub's search returns at most 1000 issues, so a search listing drops every open issue older than the newest 1000, where `--limit 10000` without one pages through them all.

For any form but `reminders-only`, run the loop's `gh issue list` command once; if it names no issue, create the standing reminders only.

Call `CronList`. A job whose prompt begins `REMINDER:` is stale when no form on this page gives that prompt on that cron, and so is a loop command other than the form's own when the form has one: `CronDelete` it. Then `CronCreate` with `recurring: true` each reminder of the form whose prompt is not already scheduled, substituting the number for `{X}` or the label for `{L}`. Then begin solving the command's first issue.

## Restart

`restart` takes the forms `start` takes, with the same shorthands and the same `--skip-label` flags, and leaves scheduled exactly the reminders of the form it names, whatever was scheduled before.

For any form but `reminders-only`, run the loop's `gh issue list` command once; if it names no issue, the form's reminders are the standing reminders only.

Call `CronList`. `CronDelete` every job that is not one of the form's reminders: a job whose prompt is not one of them, one on another cron than its reminder's, and every job but one of those that hold the same prompt. Then `CronCreate` with `recurring: true` each reminder of the form whose prompt is not scheduled after those deletions, substituting the number for `{X}` or the label for `{L}`. Then, for any form but `reminders-only`, begin solving the command's first issue.

## Reconcile issues

An issue titled `Reconcile deltahdl against <section> of IEEE 1800-2023 (<title>)` stands for one section of the standard's table of contents, read to two levels. Its body defines rules and cases and says what reconciling the section means: every rule the section states is listed with every case of it, and each case is shown by a test under `test/` that asserts the standard's outcome, or held by the open issue of its rule until a test does. A loop works every open Reconcile issue of a clause before any other issue of that clause, since the reading files the clause's issues and rewrites the ones already open. A Reconcile issue is worked by reading and filing, and it closes without a commit.

The clause's open Reconcile issues are worked one at a time, in section order, in the session itself with no agent reading, finding or filing any of it, each through these steps:

1. **List.** Read the section the issue names, every page of it, one page per Read call, and list every rule it states and every case of each. A rule is a requirement the text states: a syntax production or a restriction on it, a "shall" or "shall not", a result a tool could get observably wrong (a value, type, width, order, elaboration outcome, or VPI object, relation or property), a required error report, or a permission a tool must accept. A rule the section only refers to belongs to the clause or annex that states it, and each case of it is marked with that clause. A case is one form the rule allows or forbids, with the nearest allowed form beside each forbidden one, in each place it can be written where its handling could differ, with each kind of operand or type the rule names where the outcome could differ, and in each way of naming the construct where that matters. Write the list to `<scratchpad>/reconcile/N_rules.md`, `<scratchpad>` being the session's scratchpad directory and `N` the issue's number, so that the list outlives the context it was read in.
2. **Find.** For each case, search the whole of `test/` for the test that shows it, by the construct's source text, its diagnostic's words and its subclause, and open the test to see that it exercises that exact case and asserts the outcome the standard gives. Record the test beside the case, or record none, and note a test that asserts an outcome the standard does not give.
3. **File.** For each rule with a case that names no test, or a test asserting a wrong outcome, do step 4 of the Reconcile issue's body, filing a case that belongs to another clause or annex on the issue of its rule there: find the rule's issue, open or closed, and reopen and rewrite it, or file one, listing every case, ticked with its test or unticked, labelled exactly `IEEE 1800-2023` and the rule's own clause label, with every other clause label removed.
4. **Record.** Add the `## Rules` section of step 5 to the Reconcile issue's body through a guarded rewrite, per `.claude/memories/guarding-an-issue-body-rewrite.md`. A rule names its tests only when every case of it names one, and otherwise names its issue.
5. **Close** the Reconcile issue.

Then the clause's other issues are taken, as below.

## Other issues

A Reconcile issue is never solved alongside other issues. Each other issue is fixed for every case of its rule, per `.claude/memories/fixing-a-rule-in-full.md`, not only for the example it gives, and test first: each case's test is looked for under `test/`, per `.claude/memories/searching-for-a-test-before-adding-one.md`, written where there is none, and built and run before the code that makes it pass, and seen to fail for the reason its issue names, per `.claude/memories/verifying-through-ci.md`; a test failing for another reason has found a defect that is fixed on the spot or filed before the fix is designed. Before any of them is taken, every issue the loop lists is read, by title and, where it shares a subclause or names the same code as another, by body, and the list is sorted into groups of issues whose fixes go through the same code; the first group is taken whole, designed and tested together, and any other issues the loop lists may join it. Each commit is pushed once it closes at least one issue, and it closes as many as the work chooses to finish in it, from one group or several, with no upper limit, every case of each one's rule passing, with one `Closes #N` line per issue, per `.claude/memories/a-commit-closes-an-issue.md`, and only once the `pre-push-checks` skill, run over the committed change, prints that every check passed. An issue whose open cases cannot all land in one commit is split by rule before any of its code is written, each case of a rule it already documents staying in it.

## Stop

Call `CronList`, then `CronDelete` for every job it returns.
