# How issues are written

An issue in this repository has six sections, in this order, and every issue carries all six even when a section is one sentence.

- **Problem** — what is wrong, stated as a fact about the code, with the evidence for it and the clause of `~/LRM.pdf` it violates.
- **Why Unit Tests Did Not Catch It?** — the assertions that passed, and why they could not have failed.
- **Why Integration Tests Did Not Catch It?** — the same, for the tier that checks two components agreeing.
- **Why E2E Tests Did Not Catch It?** — the same, for the tier that drives a real entrypoint.
- **Which Unit, Integration, or E2E regression tests would prevent this from happening again?** — the tests to write, each named by the tier it belongs to and the assertion it makes.
- **Proposed Solution** — what to change.

The three backward-looking sections are the point of the format rather than padding. A defect that reached `main` got past every gate CI runs, and naming the assertion that let it through turns one report into a described gap in the suite. Answer each tier honestly, including when the honest answer is that the tier does not exist for this code: `docs/tenets/` covers the unit tier alone, so "there is no such tier here" is a finding to write down rather than a section to drop.

§11.5.1 is the worked example of what these sections are for. Every test declared its vectors `[N:0]`, where an index and a storage offset are the same number, so two elaborator paths computed offsets where indices were required and every unit test passed. The tier existed, it ran, and it could not have failed — which is exactly what the second section asks a writer to state, and stating it is what turns the defect into the missing `[N:M]` case.

The regression section is those three read forwards, and it is where the coverage owed is named. Each entry says which tier the test sits in, what it declares, and what it asserts, so that the test can be written from the issue without rediscovering the defect. It is separate from the solution because a fix and the test that would have caught it are separate pieces of work, and folding the second into the last paragraph of the first tends to ship the fix alone.

Take the vocabulary from the standard. Clause and subclause, elaboration, declaration, net and variable — the words `~/LRM.pdf` uses for the thing being described, with the clause number cited wherever a claim rests on one.

Write plain, ordinary English prose. Tables where a table genuinely reads better than a paragraph, bullets only when enumerating things, never to break up an argument.

The tier vocabulary and what each tier is for come from `docs/tenets/` — see [reading-the-tenets](reading-the-tenets.md). What closes the issue when the fix lands is in [issue-closing-keywords](issue-closing-keywords.md).
