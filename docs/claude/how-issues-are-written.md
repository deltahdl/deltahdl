# How issues are written

An issue about the program has six sections, in this order, and every issue about the program carries all six even when a section is one sentence.

- **Problem** — what is wrong, stated as a fact about the code, with the evidence for it and the clause of `~/LRM.pdf` it violates.
- **Why Unit Tests Did Not Catch It?** — the assertions that passed, and why they could not have failed.
- **Why Integration Tests Did Not Catch It?** — the same, for the tier that checks two components agreeing.
- **Why E2E Tests Did Not Catch It?** — the same, for the tier that drives a real entrypoint.
- **Which Unit, Integration, or E2E regression tests would prevent this from happening again?** — the tests to write, each named by the tier it belongs to and the assertion it makes.
- **Proposed Solution** — what to change.

An issue about anything else has two sections, **Problem** and **Proposed Solution**, and owes no tests at all.

The program is the code a test tier can run. That is the simulator sources under `src/` and the C++ beside them in `lib/`, the Python under `scripts/` and `lib/python/`, and the Python and C++ under `test/` that computes the values assertions rest on — the fixtures, the helpers, and the readings of the standard such as `lib/python/reserved_words/`, each of which carries its own `unit/` directory under `test/` and its own coverage gate. A defect in any of that got past a tier which exists and could have failed. Naming the assertion that let it through is what turns one report into a described gap in the suite.

The workflow files under `.github/workflows/`, the linter configurations under `etc/`, the CMake files and the documentation are not the program, because no tier runs them. A test written against one of those files opens it, reads a value back and asserts the value it just read. It cannot fail for a reason worth knowing, and it goes red for reasons that are not worth knowing: a step renamed, a rule added deliberately, a job split in two.

That a program module could be extended to police a configuration file does not make that file program code, and this is the trap the six-section form sets. The worked example is an issue over three workflows carrying three copies of one yamllint rule set. Written in the six-section form, it answered "why did the unit tier not catch it" by describing what the Python module reading those workflows did not read out of a `run:` block, and then asked for two new unit tests comparing the copies. The defect is one decision written down three times, and the fix is to write it once — after which the tests the fourth section asked for have nothing left to compare. Under the two-section form neither those tests nor the paragraphs arguing for them get written.

Decide by what the defect is in, not by what the fix touches and not by what a gate could be made to notice. A defect in the elaborator whose fix also edits a workflow file is a program issue and gets all six sections. A defect confined to workflows, linter configuration or build files is not a program issue, however much program behaviour those files move.

The assertions are the other side of `test/`. A unit test that checks the wrong thing, checks nothing, or checks a value it just read is a defect in the coverage rather than in the program, so it gets two sections. So does a SystemVerilog fixture that declares the wrong thing. Asking why the unit tests did not catch a defective unit test answers itself.

Within a program issue, the three backward-looking sections are the point of the format rather than padding. A defect that reached `main` got past every gate CI runs, and naming the assertion that let it through turns one report into a described gap in the suite. Answer each tier honestly, including when the honest answer is that the tier does not exist for this code. `docs/tenets/` covers the unit tier alone, so "there is no such tier here" is a finding to write down rather than a section to drop.

§11.5.1 is the worked example of what these sections are for. Every test declared its vectors `[N:0]`, where an index and a storage offset are the same number, so two elaborator paths computed offsets where indices were required and every unit test passed. The tier existed, it ran, and it could not have failed. That is exactly what the second section asks a writer to state, and stating it is what turns the defect into the missing `[N:M]` case.

The regression section is those three sections read forwards, and it is where the coverage owed is named. Each entry says which tier the test sits in, what it declares, and what it asserts, so that the test can be written from the issue without rediscovering the defect. It is separate from the solution because a fix and the test that would have caught it are separate pieces of work. Folding the second into the last paragraph of the first tends to ship the fix alone.

Take the vocabulary from the standard. Clause and subclause, elaboration, declaration, net and variable — the words `~/LRM.pdf` uses for the thing being described, with the clause number cited wherever a claim rests on one.

Write the issue in plain English, to the same rules as everything else written here. They are in [write-the-exact-name](write-the-exact-name.md) for the words a name is written in, in [lead-with-what-it-is-for](lead-with-what-it-is-for.md) for what comes before the first identifier, and in `docs/tenets/conventions/README.md` for the generic form of both.

The tier vocabulary and what each tier is for come from `docs/tenets/` — see [reading-the-tenets](reading-the-tenets.md). What closes the issue when the fix lands is in [issue-closing-keywords](issue-closing-keywords.md).
