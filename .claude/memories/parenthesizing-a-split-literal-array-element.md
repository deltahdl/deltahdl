---
name: parenthesizing-a-split-literal-array-element
description: "An element of a const char* array written as adjacent string literals is wrapped in parentheses, or Clang's -Wstring-concatenation fails the test build."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 84445ccd-f1b9-420f-afbd-5b1a412da9aa
  modified: 2026-11-08T20:36:47.716Z
---

# Parenthesizing a split-literal array element

When an element of a `const char* const kSources[]` array (or any array of string literals) is written as two or more adjacent literals across lines, wrap that element in parentheses: `("module m;\n" "endmodule\n"),`. The CI coverage build compiles tests with `-Werror`, and Clang's `-Wstring-concatenation` reads adjacent literals in an array initializer as a comma left out, so the whole test file fails to build and none of its tests run.

The warning does not fire for every such element. Clang suppresses it when most elements of the array are split, and fires on one that ends the array or stands among single-literal neighbours. Adding or moving one element can therefore turn a file that built into one that does not. Parenthesizing every multi-literal element of an array you add or extend avoids the guess.

**Why:** a missing pair of parentheses costs a full CI round. The build failure hides every test in the file, so whatever those tests would have shown comes a round later still.

**How to apply:** after writing or extending a source array in a test, parenthesize each element made of more than one literal before pushing. clang-format keeps the parentheses and only re-indents the continuation lines. See [verifying-through-ci](verifying-through-ci.md).
