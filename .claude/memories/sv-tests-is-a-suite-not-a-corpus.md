---
name: sv-tests-is-a-suite-not-a-corpus
description: "Call sv-tests a suite, its checkout a revision and its program deltahdl; never \"corpus\", \"runner\", \"score\" or \"the tool\", in code, commit messages, issues or memories"
metadata: 
  node_type: memory
  type: feedback
---

# sv-tests is a suite, never a corpus

sv-tests is a test suite; each file in it is a test. Write "suite", "the
suite's tag", "sv-tests revision" followed by the checkout's hash, "deltahdl rejected the code", and
"evaluate" for what `scripts/run_sv_tests` does with a test's outcome. Never
write "corpus", "runner", "score" or "the tool" unless quoting an old real log.

**Why:** "corpus", "runner", "score" and "the tool" are words sessions coined
and repeated as if established; they are not the suite's own words.

**How to apply:** when touching an issue that mentions sv-tests at all —
editing its body, commenting on it, or only labelling it — grep its title and
body for these words first and rewrite them, even in sentences the touch does
not otherwise change, since an older issue may still carry them. A quoted log
line from a run that printed the old wording (`tool rejected the file under …, but the
corpus tags it …`) stays as quoted. See [[single-edition-1800-2023]] and
[[reading-the-sv-tests-log-first]].
