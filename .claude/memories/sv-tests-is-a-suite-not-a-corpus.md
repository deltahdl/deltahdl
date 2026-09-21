---
name: sv-tests-is-a-suite-not-a-corpus
description: "Call sv-tests a suite, its checkout a revision and its program deltahdl; never \"corpus\", \"runner\", \"score\" or \"the tool\", in code, commit messages, issues or memories"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 7829aa59-f8bc-4f09-b395-224467199b68
  modified: 2026-09-19T13:04:54.514Z
---

# sv-tests is a suite, never a corpus

sv-tests is a test suite; each file in it is a test. Write "suite", "the
suite's tag", "sv-tests revision" followed by the checkout's hash, "deltahdl rejected the code", and
"evaluate" for what `scripts/run_sv_tests` does with a test's outcome. Never
write "corpus", "runner", "score" or "the tool" unless quoting an old real log.

**Why:** "corpus", "score" and "the tool" were words an earlier session coined
and later ones repeated as if established; the user asked on 2026-09-18 that
nothing say them (commits 62820847e, ee91791f8, e4254f8a7). On 2026-09-19 the
user found "corpus" still in issue #2930 after a session had edited it without
noticing.

**How to apply:** when touching an issue that mentions sv-tests at all —
editing its body, commenting on it, or only labelling it — grep its title and
body for these words first and rewrite them, even in sentences the touch does
not otherwise change: on 2026-09-21 the user found "corpus" and "the tool" in
#3637 after this session had labelled it twice without reading it, the body
having been filed on the morning of 2026-09-18, before the words were banned.
The 34 open sv-tests issues were rewritten that day; a quoted log line from
a run that printed the old wording (`tool rejected the file under …, but the
corpus tags it …`) stays as quoted. See [[single-edition-1800-2023]] and
[[reading-the-sv-tests-log-first]].
