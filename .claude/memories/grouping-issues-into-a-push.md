---
name: grouping-issues-into-a-push
description: "A push solves every open issue of one matter, meaning one clause of IEEE 1800-2023 fixed in one subsystem of deltahdl. The matter bounds the batch, never a count. The batch is solved in the working tree and committed once. Changes to what verifies or what everything runs through go alone."
metadata:
  type: feedback
---

# Grouping issues into one push

A push solves a batch made of every open issue that shares one matter. The matter bounds the batch, never a count. Two issues share a matter when both of these hold:

- **Clause.** They fall under the same clause of IEEE 1800-2023. That is the issue's `§N` or `Annex X` label, narrowed to the same subclause subtree where the titles name one. An sv-tests issue counts under the 2023 clause its design exercises, never under its 2017 tag.
- **Subsystem.** Their fixes land in the same directory under `src/`: `lexer`, `preprocessor`, `parser`, `elaborator`, `simulator`, `synthesizer`, `driver` or `common`. The unit test files that go with them are named after the same subsystem, as in `test_<subsystem>_subclause_…`.

**Why:**

- **Waiting.** Each push waits out a CI run of ten to twenty minutes, and nothing else happens while it runs ([[waiting-while-a-ci-run-is-in-progress]]). With one issue per push, every issue pays that wait. A batch of n issues shares the wait n ways.
- **Shared reading.** Issues of one clause and subsystem are read from the same LRM pages and fixed in the same source and test files, so the reading done for the first serves the rest.
- **Visible interactions.** When two fixes interact, the interaction lies in code already open. This covers a test written against behaviour that a neighbouring fix changes. Spread across subsystems, such disagreements show up only in the run.
- **Traceable red runs.** A red run has to be traced to the issue that caused it. Within one matter, a failing job points at a file the batch touched and the session has open, however many issues the batch holds. A batch that spans subsystems turns every failing job into a search through unrelated changes. What makes a batch too big to trace is the number of matters it mixes, not the number of issues it holds, so a count would cap the wrong thing.

**How to apply:**

1. **Seed.** Take the issue the loop's selection command names as the seed.
2. **Gather.** Add every open issue of the seed's matter, nearest subclause first. When a matter is too broad to hold in mind at once, narrow it to the seed's subclause subtree, such as §21.2 rather than §21. Narrow it this way, never by capping the count.
   - Leave out every issue labelled 'needs decision'.
   - Take an issue the batch depends on into the batch, ahead of the issues that wait on it.
   - Bring each issue up to date before starting it.
   - When an issue's subsystem cannot be told without investigating it, take it in. If its fix turns out to land elsewhere, it leaves the batch and seeds a later one.
3. **Solve.** Solve the issues one after another in the working tree, tests first, and commit nothing until the last one is done, per [[one-commit-is-a-whole-body-of-work]]. As each issue is finished, write its paragraph of the commit message into the scratchpad, so that nothing depends on the context outlasting the batch.
   - An issue that turns out to need a person's decision is labelled for one. Its edits come out of the tree before the commit.
   - A finding made on the way joins the batch when it is of the batch's matter. Otherwise it seeds the next batch ([[solving-what-a-session-finds]]).
4. **Commit.** Commit once.
   - The subject joins each issue's leading clause with `; `.
   - The body gives each issue its own paragraph.
   - The message ends with one `Closes #N` line per issue ([[one-closing-keyword-per-issue]]).
5. **Push and read the run.** When the run goes red, trace each failing job to the issue whose change it names, and fix it per [[fixing-a-red-run]]. When an issue's fix cannot be repaired, revert it and reopen the issue per [[a-revert-does-not-reopen]].

Some changes go in a push of their own and are never batched:

- A change to CI, to the workflows, to the build, to a test fixture or helper that other clauses' tests share, or to a grammar path that every test goes through. Such a change alters what verifies the batch or what everything else runs through, so its fallout would hide the batch's own results.
- The fix for a red run.

A change under `.claude/`, such as a memory or a skill, can join any batch, since only the Markdown lint checks it.
