---
name: what-does-not-get-filed
description: "Do not file a case of a rule the commit in hand fixes, or a case of a rule an open issue already documents; the first joins the fix, the second joins that issue."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 86699205-8167-4d43-95d1-668dd7cf1a13
  modified: 2026-10-28T14:38:19.818Z
---

# What does not get filed

Two findings do not become issues of their own.

A case of a rule the commit in hand fixes. The fix reaches it, its test joins the commit, and the commit message states it ([[fixing-a-rule-in-full]]).

A case of a rule an open issue already documents. It is added to that issue's list of cases instead.

**Why:** A second issue over one rule gives one piece of work two entries. Closing either leaves the other claiming there is something left, or leaves the rule half-fixed under a closed issue.

**How to apply:** Before filing anything, whether a finding of research per [research-lives-in-issues](research-lives-in-issues.md) or one the user asked to have tracked, ask whether the change in hand already reaches it, and search the tracker for an open issue of its rule. Everything else is filed, per [solving-what-a-session-finds](solving-what-a-session-finds.md).
