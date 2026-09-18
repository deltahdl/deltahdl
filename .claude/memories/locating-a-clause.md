---
name: locating-a-clause
description: "Resolve an LRM clause to a page through the Read tool alone, never pypdf; the printed page number is the physical page minus one."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: ec269662-372b-4932-ad5a-23c29f07e1d6
  modified: 2026-09-15T01:53:06.168Z
---

# Locating a clause in the PDF

`~/LRM.pdf` is IEEE 1800-2023, 1354 PDF pages. The printed page number is the physical page minus one: §10.1 General is physical page 248, printed 247.

Locate a clause with the Read tool and nothing else: read the contents pages at the front of the PDF, or jump from a landmark below by the printed-page rule, then Read the resolved physical pages one per call, per [reading-the-lrm-one-page-per-call](reading-the-lrm-one-page-per-call.md).

**Why:** On 2026-09-14 the user saw a `pypdf` bookmark walk being used to find a page and said: "You can read PDFs directly through your Read tool. Yet you are using pypdf." An earlier version of this note recommended that walk as a metadata-only shortcut; the user does not want `pypdf` used on the LRM at all — see also [not-converting-the-lrm-to-text](not-converting-the-lrm-to-text.md).

**How to apply:** Never import `pypdf` against `~/LRM.pdf`, not even for the outline. Landmarks (physical pages) found so far:

- Clause 10 "Assignment statements": 248 to 269, ending at §10.11; clause 11 starts at 270. There is no §10.12, §10.13 or §10.14.
- §16.1 General, §16.2 Overview and §16.3 Immediate assertions: 384.
- §16.5 Concurrent assertions overview and §16.5.1 Sampling: 394.
- §16.8 Declaring sequences: 403. §16.9.11 Composing sequences: 431.
- §16.12 Declaring properties: 440. §16.12.1 Property instantiation: 444.
- §16.13.6 Sequence methods: 472.
- §16.14 Concurrent assertions: 476. §16.14.1 Assert statement: 477. §16.14.5 Outside procedural code: 481. §16.14.6 Embedding in procedural code: 482.
- Contents page listing clauses 19.6 through 22.10: 17.
- §22.5 `define, `undef, and `undefineall and §22.5.1 `define: 707, running to 709, where Syntax 22-3 gives the text macro usage. §22.12 `line and §22.13 `__FILE__ and `__LINE__: 721.

Add a landmark here whenever a session resolves a clause it had to hunt for.
