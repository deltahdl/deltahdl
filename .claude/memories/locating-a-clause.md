---
name: locating-a-clause
description: "Resolve an LRM clause to a page through the Read tool alone, never pypdf: the contents pages at physical 11 to 27 list every clause to two levels, and the printed page number is the physical page minus one."
metadata: 
  node_type: memory
  type: feedback
---

# Locating a clause in the PDF

`~/IEEE 1800-2023.pdf` is IEEE 1800-2023, 1354 PDF pages. The printed page number is the physical page minus one: §10.1 General is physical page 248, printed 247.

Locate a clause with the Read tool and nothing else, one page per call, per [reading-the-lrm-one-page-per-call](reading-the-lrm-one-page-per-call.md). Read the contents page that lists the clause, add one to the printed page it gives, and Read that physical page.

**Why:** The Read tool reads PDFs directly, and the user does not want `pypdf` used on the LRM at all, not even for its bookmarks — see also [not-converting-the-lrm-to-text](not-converting-the-lrm-to-text.md). The contents pages resolve any first- or second-level clause in one read, so a list of clauses they already give saves nothing.

**How to apply:** Never import `pypdf` against `~/IEEE 1800-2023.pdf`, not even for the outline. The contents pages, by physical page, each listing clauses to two levels:

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
- §6.6.8 Generic interconnect: 100. §7.3.2 Tagged unions: 152. §7.4.3 Memories and §7.4.4 Multidimensional arrays: 155. §7.4.6 Operations on arrays: 158. §7.8.5 to §7.8.7: 166. §7.10.3 and §7.10.4: 173. §7.12.3 Array reduction methods: 177.
- §8.26.6.1 Method name conflict resolution: 213. §8.26.6.2 and §8.26.6.3: 214.
- §9.3.3: 229. §9.3.4: 230. §9.3.5: 231. §9.4.2.1: 234. §9.4.2.3 and §9.4.2.4: 236. §9.4.3 and §9.4.4: 237. §10.6.1 and §10.6.2: 258.
- §11.3.5 and §11.3.6: 275. §11.4.5 Equality operators: 280. §11.4.10 Shift operators: 285. §11.4.12 Concatenation operators: 287. §11.4.12.2 and §11.4.13: 289. §11.4.14 Streaming operators: 291, with §11.4.14.2 and §11.4.14.3 on 293. §11.10.1 and §11.10.2: 306.
- §12.4.1: 317. §12.4.2: 318. §12.5.1 and §12.5.2: 323. §12.5.4: 325. §12.6.2: 329. §12.6.3 and §12.7: 330. §12.7.1: 331. §12.7.4 to §12.7.6: 334. §13.3.1: 340. §13.4.1: 343. §13.4.3: 346.
- §18.4.1 and §18.4.2: 528. §18.5.2: 531. §18.5.6: 537. §18.5.7 and §18.5.7.1: 538. §18.5.12 Constraint guards: 544. §18.5.13.2 Disabling soft constraints: 550. §18.17.4 and §18.17.5: 570. §18.17.7: 572. §22.5.2 and §22.5.3: 713.

Add to that list only what the contents cannot give — a subclause below the second level, or a located list, table or syntax box — and only when reaching it took more than one page read after the contents page. A clause a contents page resolves is never recorded. An entry that qualifies goes into the commit of the work it served, as a trailing clause of that subject, never as a commit of its own.
