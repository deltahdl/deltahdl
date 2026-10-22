---
name: names-say-what-a-thing-does
description: "An identifier names what its thing is or does; a clause, table, figure or annex number, or a bare serial, is never what tells it apart."
metadata:
  node_type: memory
  type: feedback
  originSessionId: bda8a375-8175-4a84-a8b2-3ae4426fb762
  modified: 2026-10-22T23:33:54.842Z
---

# Names say what a thing does

Every identifier, whether a type, function, fixture, constant or variable, in
`src/`, `lib/`, `test/` or `scripts/`, is named for what the thing is or does.
A clause, subclause, table, figure or annex number is a citation. It belongs
in a comment or, for a unit test file, in the file name the house convention
gives it, never as the part of an identifier that tells it apart from its
neighbours. A serial suffix such as `Src43` is no better. `ParseTimescale31402`
should be something like `PreprocessAndParse`, and `kTable221` should name the
keywords the table lists.

Names that stand for a real thing keep their digits. That covers an edition
(`kVer13641995`, `Verilog2005KeywordList`), a name the standard itself mandates
(`vpiMode1364v1995`, per [[standard-names-listed-explicitly]]), an algorithm
(`aes128`) and a literal written into a test name (`hFFFF00000001`).

**Why:** The user wants names a reader understands without opening the
definition. A number makes the reader look the definition up, and it goes
stale, because a helper written for one subclause's tests comes to serve
others. Once clang-tidy's naming rule strips the dots out, the number stops
working even as a citation, since `31402` no longer reads as `3.14.2`.

**How to apply:**

- Name a new helper for the action it takes and the result it returns.
- When a naming check refuses a name, rename it by meaning rather than
  deleting the characters the check objects to ([[const-local-naming]]).
- When an existing name of this kind turns up, file an issue for it unless an
  open one already covers it ([[solving-what-a-session-finds]]).
- The struct a refactor groups parameters into is named after the entity the
  standard defines ([[lrm-guides-structure]]). That entity's name, never its
  clause number, is what goes into the identifier.
