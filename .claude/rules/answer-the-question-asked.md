# Answer the question that was asked

Put the answer in the first sentence, and give it the fewest sentences that state it. Add a reason only where the reason changes what the reader would do next. Cut every sentence that is in the draft because it is true rather than because it is needed.

A long answer costs the reader the work of finding which sentence answered them, and a reader who picks the wrong sentence leaves with something the writer never said. On 2026-08-06 the user asked what one of the two dead-code steps added under #2996 checks, read three replies over about an hour, and then wrote out both checks themselves. One of the two they wrote was a third condition that neither step tests, and that no step needs to test, because the compiler already reports it. What was owed was one sentence: the `Check every lib/cpp helper is used outside its own declaration` step in `.github/workflows/deltahdl.yml` reports an `inline` function declared in a header under `lib/cpp/` that nothing anywhere uses.

Explain a check, a gate or a test by what makes it fail. Say what it reads and what makes it report, and say that before the reason it exists. Give the reason only when it is asked for.

Write the comment above a check to the same length as the answer would be. The comments above the two steps added under #2996 are long enough that the steps had to be explained again in a session, which is the work a comment is there to save.

[lead-with-what-it-is-for](lead-with-what-it-is-for.md) orders a purpose ahead of the identifiers, and it governs a document written for a reader who asked nothing: an issue body, a note here, a docstring. This note governs a reply to a question. There the answer comes first, and the purpose comes only if the question asked for it. Nothing enforces either, so a green `Documentation` run is not agreement.
