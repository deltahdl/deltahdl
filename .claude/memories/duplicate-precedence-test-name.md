---
name: duplicate-precedence-test-name
description: `Precedence.BitwiseOrHigherThanLogicalAnd` stood in two files over §11.3.2; the right-operand case was renamed in 30aff9f54.
metadata:
  type: project
---

# The precedence name that stood in two files

§11.3.2 once had `Precedence.BitwiseOrHigherThanLogicalAnd` declared in two files: `a && b | c` in one and `a | b && c` in the other, the right-operand and left-operand cases of one precedence rule. The coverage was deliberate, so the fix was a rename rather than a deletion, and the right-operand case became `BitwiseOrHigherThanLogicalAndOnRight` in `30aff9f54`.

Supports [unique-test-names](../rules/unique-test-names.md).
