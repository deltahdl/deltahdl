---
name: what-does-not-get-filed
description: "A case of the part of a rule the commit in hand fixes joins the fix, and a case of a part an open issue documents joins that issue; any other finding of a rule is filed unless its whole part joins the commit, and only a defect with no rule behind it is fixed on the spot."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 86699205-8167-4d43-95d1-668dd7cf1a13
  modified: 2026-11-21T02:53:56.911Z
---

# What does not get filed

Two findings do not become issues of their own:

- A case of the rule, or the part of a rule ([one-indivisible-problem-per-issue](one-indivisible-problem-per-issue.md)), that the commit in hand fixes. The fix reaches it, its test joins the commit, and the commit message states it ([fixing-a-rule-in-full](fixing-a-rule-in-full.md)).
- A case of a rule or part an open issue already documents. It is added to that issue's list of cases instead.

Any other finding of a standard's rule is filed, unless the work in hand takes up that whole rule or part too, every case tested, and the same push finishes it ([a-push-closes-an-issue](a-push-closes-an-issue.md)). One case of another rule is never fixed on its own. A defect with no rule behind it, such as a misleading message or a fault in a script, is fixed on the spot when that is quicker and safer than filing it, and filed otherwise.

**Why:** A second issue over one part of a rule gives one piece of work two entries. Closing either leaves the other claiming there is something left, or leaves the part half-fixed under a closed issue. A lone case of another rule fixed in passing leaves that rule's other cases as broken as before, with nothing on record to say so.

**How to apply:** Before filing anything, whether a finding of research per [research-lives-in-issues](research-lives-in-issues.md) or one the user asked to have tracked, ask whether the change in hand already reaches it, and search the tracker for an open issue of its rule or part ([searching-for-an-existing-report-before-filing](searching-for-an-existing-report-before-filing.md)).
