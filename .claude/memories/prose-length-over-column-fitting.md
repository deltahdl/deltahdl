---
name: prose-length-over-column-fitting
description: A shorter word chosen to fit a column is paid for out of the accuracy the prose exists to carry.
metadata:
  type: feedback
---

# Accuracy over fitting a column

The shorter word chosen to fit a column is paid for out of the accuracy the prose exists to carry. Write what is true and let the line be as long as that takes.

**Why:** A width limit is arbitrary against the thing being described, so every time the two conflict the description loses. The cost is invisible afterwards, because what the prose would have said is not in the file to compare against.

**How to apply:** Where a limit really is enforced, move rather than compress: split the file, split the comment, or take the text somewhere that has room. `.github/workflows/deltahdl.yml` is built around this. Its file-line cap **fails at 950 lines**, so 949 is the most a `.cpp` or `.h` under `src`, `test` or `lib/cpp` may hold. It used to fail at 1001 and merely warn from 950, and the warning is exactly what this rule predicts will not work: nothing has to answer a warning, so files sat in the band across change after change until one carried them past 1000 and the cheapest repair was to fold a comment shorter — which is what `cc443c650` did to return `src/parser/parser_port.cpp` to 1000. `5a1d05c1c` emptied the band and made the number the job enforces the number it names. See also [commit-subject-length](commit-subject-length.md).
