---
name: prose-length-over-column-fitting
description: A shorter word chosen to fit a column is paid for out of the accuracy the prose exists to carry.
metadata:
  type: feedback
---

# Accuracy over fitting a column

The shorter word chosen to fit a column is paid for out of the accuracy the prose exists to carry. Write what is true and let the line be as long as that takes.

**Why:** A width limit is arbitrary against the thing being described, so every time the two conflict the description loses. The cost is invisible afterwards, because what the prose would have said is not in the file to compare against.

**How to apply:** Where a limit really is enforced, move rather than compress: split the file, split the comment, or take the text somewhere that has room. `.github/workflows/deltahdl.yml` is built around this. Its file-line cap fails at 1001 lines but warns from 950, because a file sitting at exactly 1000 passes silently and the cheapest repair at 1001 is to fold a comment shorter — which is what `cc443c650` did to return `src/parser/parser_port.cpp` to 1000. The warning exists to put the split in front of the author while there are still 50 lines to write it in. See also [commit-subject-length](commit-subject-length.md).
