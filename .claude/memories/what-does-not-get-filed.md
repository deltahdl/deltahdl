---
name: what-does-not-get-filed
description: Do not file a defect the commit in hand fixes, or one an open issue already covers.
metadata:
  type: feedback
---

# What does not get filed

Two findings do not become issues.

A defect the commit in hand fixes. The commit message states it and the issue would close on the same push.

A defect an open issue already covers. Cite that issue instead.

**Why:** A second issue over one defect gives one piece of work two entries, and closing either leaves the other claiming there is something left.

**How to apply:** Before filing, ask whether the change in hand already closes it, and search the tracker for an existing one. Everything else gets filed, per [filing-what-a-session-finds](filing-what-a-session-finds.md).
