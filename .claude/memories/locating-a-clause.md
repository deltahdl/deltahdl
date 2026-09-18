---
name: locating-a-clause
description: "Resolve an LRM clause to a page through the Read tool alone, never pypdf: the contents pages at physical 11 to 27 list every clause to two levels, and the printed page number is the physical page minus one."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: ec269662-372b-4932-ad5a-23c29f07e1d6
  modified: 2026-09-18T00:00:00.000Z
---

# Locating a clause in the PDF

`~/LRM.pdf` is IEEE 1800-2023, 1354 PDF pages. The printed page number is the physical page minus one: §10.1 General is physical page 248, printed 247.

Locate a clause with the Read tool and nothing else, one page per call, per [reading-the-lrm-one-page-per-call](reading-the-lrm-one-page-per-call.md). Read the contents page that lists the clause, add one to the printed page it gives, and Read that physical page.

**Why:** On 2026-09-14 the user saw a `pypdf` bookmark walk being used to find a page and said: "You can read PDFs directly through your Read tool. Yet you are using pypdf." An earlier version of this note recommended that walk as a metadata-only shortcut; the user does not want `pypdf` used on the LRM at all — see also [not-converting-the-lrm-to-text](not-converting-the-lrm-to-text.md).

Until 2026-09-18 this note also grew a landmark list by one entry per lookup, each entry committed to `main` on its own, and told every session to keep adding to it. The user asked whether that was useful. It was not: the contents pages already resolve any first- or second-level clause in one read, so most entries saved nothing, and the standing order produced commits whose whole content was a page number. The map below replaces it.

**How to apply:** Never import `pypdf` against `~/LRM.pdf`, not even for the outline. The contents pages, by physical page, each listing clauses to two levels:

| Physical page | Lists |
| --- | --- |
| 11 | §1 to §4.9 |
| 12 | §4.10 to §7.1 |
| 13 | §7.2 to §8.30 |
| 14 | §9 to §12.8 |
| 15 | §13 to §16.9 |
| 16 | §16.10 to §19.5 |
| 17 | §19.6 to §22.10 |
| 18 | §22.11 to §26.4 |
| 19 | §26.5 to §30.2 |
| 20 | §30.3 to §34.5 |
| 21 | §35 to §37.18 |
| 22 | §37.19 to §37.68 |
| 23 | §37.69 to §38.29 |
| 24 | §38.30 to Annex B |
| 25 | Annex C to Annex G |
| 26 | Annex H to §O.2 |
| 27 | §O.3 to Annex Q |

The contents stop at the second level, so a deeper subclause or a particular list, table or syntax box inside a long clause still takes paging forward from the clause's first page. Those found so far, by physical page:

- §16.9.11 Composing sequences: 431. §16.12.1 Property instantiation: 444. §16.13.6 Sequence methods: 472.
- §16.14.1 Assert statement: 477. §16.14.5 Outside procedural code: 481. §16.14.6 Embedding in procedural code: 482.
- §18.5.3 Distribution: 532 to 535, with its limitations list (no `dist` on a `randc` variable, at least one `rand` variable) on 534. §18.5.4 Uniqueness constraints: 535.
- §21.2.1's rules for string literal and expression arguments: 656.
- §22.5.1 `define: 707 to 709, where Syntax 22-3 gives the text macro usage.

Add to that list only what the contents cannot give — a subclause below the second level, or a located list, table or syntax box — and only when reaching it took more than one page read after the contents page. A clause a contents page resolves is never recorded. An entry that qualifies goes into the commit of the work it served, as a trailing clause of that subject, never as a commit of its own.
