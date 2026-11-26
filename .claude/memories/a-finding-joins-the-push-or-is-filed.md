---
name: a-finding-joins-the-push-or-is-filed
description: "A finding related to the issues the push is solving goes in that push, and every other finding is filed, a case of an open issue's problem on that issue; nothing is fixed on the spot outside that work."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 86699205-8167-4d43-95d1-668dd7cf1a13
  modified: 2026-11-21T02:53:56.911Z
---

# A finding joins the push or is filed

A finding related to the issues the push is solving goes in that push, and every other finding is filed. The one rule covers every kind of finding, whether it breaks a rule of a standard or has no rule behind it, such as a misleading message or a fault in a script.

- **Related** is a case of the problem one of the push's issues holds ([one-indivisible-problem-per-issue](one-indivisible-problem-per-issue.md)), whether under a rule of a standard or in deltahdl itself. The fix reaches it, its test joins the push, and the commit that fixes it says so ([fixing-a-problem-in-full](fixing-a-problem-in-full.md)).
- **Anything else** is filed. A case of a problem an open issue already holds is added to that issue's list of cases; the rest becomes an issue of its own. Its issue may join the push whole, as one more issue the push closes ([a-push-closes-an-issue](a-push-closes-an-issue.md)), but never as one case fixed in passing.

**Why:** A second issue over one problem gives one piece of work two entries, and closing either leaves the other claiming there is something left. A finding fixed in passing lands with no issue, so the tracker never shows it was found, and for a rule of a standard the rule's other cases stay as broken as before with nothing on record to say so.

**How to apply:** Before filing anything, whether a finding of research per [research-lives-in-issues](research-lives-in-issues.md) or one the user asked to have tracked, ask whether it is related to the issues the push is solving, and search the tracker for an open issue of its problem ([searching-for-an-existing-report-before-filing](searching-for-an-existing-report-before-filing.md)).
