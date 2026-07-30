# Reading the tenets

`docs/tenets/` holds the rules a test suite is held to. Read the ones
covering the tier a change touches before writing the change, not as a
check afterwards. They decide what a test has to do to count, which is
information needed while the test is being written.

The tenets are generic and this repository conforms to them. A tenet names
no language, no tool, no directory and no count, so it never restates the
layout, the gate names or the inventories that `CLAUDE.md` and the tree
already state correctly. Anything written into a tenet that the repository
also states is a copy, and it drifts with nothing to signal it — the same
reasoning that keeps these notes out of one machine's local memory
([where-notes-live](where-notes-live.md)).

## Why the tree exists

On 2026-07-29 a §11.5.1 defect was traced to a suite-wide blind spot
rather than to a missing test. Two elaborator paths synthesized a select
using a bit's storage offset where its declared index was required. That
is wrong for `wire [8:1] w`, where the index is one above the offset at
every bit, and correct for `wire [7:0] w`, where the two are the same
number. Every test in the suite declared its vectors in the second form,
or drove the assignment from a literal, which carries no declared range at
all. The faulty arithmetic ran in many tests and was never once given an
input that could expose it.

Nothing already written down would have prevented that. The four test
notes here — [test-driven-development](test-driven-development.md),
[test-file-letter-suffixes](test-file-letter-suffixes.md),
[unique-test-names](unique-test-names.md) and
[diagnosing-sv-tests-failures](diagnosing-sv-tests-failures.md) — cover
authoring order, file naming, case naming and failure reading. All four
are mechanics. None says anything about which values a test should supply,
and the one quality bar that is enforced, a 100% coverage gate, is
satisfied in full by a suite that only ever supplies the value where being
wrong and being right look identical.

The user's framing was that this is testing 101, and it is: choose inputs
that can distinguish correct code from incorrect code. It belongs in a
tenet rather than in a note here because it is true of any suite in any
language, and because a rule about how to test cannot live only in the
notes describing how this repository happens to test today.
