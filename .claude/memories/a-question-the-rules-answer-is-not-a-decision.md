---
name: a-question-the-rules-answer-is-not-a-decision
description: "Before labelling an issue 'needs decision', check whether the standing reminders, the issue or the standards (1800-2023 and 1800.2-2020, and the clauses that cite, parallel or are named by the rule) already answer the question; if one does, act on it"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 51a015a3-4652-42ac-8c15-ce1bc6f6ae12
  modified: 2026-11-21T02:56:28.614Z
---

# A question the rules answer is not a decision

An issue is labelled 'needs decision' only for a question that the autopilot skill's standing reminders, the issue itself, the linked issues and the standards all leave open. A question they answer is acted on, with its answer and what the answer rests on written into the issue.

**Why:** A question the rules already answer has its answer; labelled 'needs decision', it parks the issue on a person who can only restate that answer. Questions of order are the usual case, between issues the loop selects as much as anywhere: the reminder to solve whatever issues the original one depends on answers them.

**How to apply:** Test the question against each reminder and against the blocked-by links. For a question of what the language allows, read the rule in both `~/IEEE 1800-2023.pdf` and `~/IEEE 1800.2-2020.pdf` and write what each says into the issue, pages included; the 2017 edition is no source of truth ([single-edition-1800-2023](single-edition-1800-2023.md)), and a library's code is not one either ([a-library-is-not-a-standard](a-library-is-not-a-standard.md)). Then read the standard these ways before calling anything open, each followed by a clause where it settled a question:

- **Beyond the clause.** The clause stating the parallel rule for a sibling construct, every clause that cites this one and every clause it names often settle what it leaves open (§16.3 and §17.3 make §16.14's list of places the whole grant).
- **A list is a summary.** When a rule lists constructs that have subclauses of their own, read each listed subclause before weighing readings of the list's wording (§34.5.10 to §34.5.14 and §34.5.20.2 fill in §34.5.27.2's list).
- **The premise.** When a question asks how two of deltahdl's own entities relate, check that the standard defines both. If one is only an artifact of the implementation, the question does not arise and the issue is a defect (§19.9 loads coverage per covergroup type, so a saved instance has no identity question to settle).
- **An open sentence covers only what it names.** Read every other sentence of the clause and the definition of each term it uses before calling anything beside an "implementation-specific" sentence open (§34.5.32.2 with §34.4's definition of an envelope).
- **Clause 37 in full.** Read every numbered detail to the end, examples included, and follow every arrow in Clause 37 that reaches the class, not only those in its own subclause; the vpiParent and prefix details often name the object (§37.17 detail 26 and §37.16 detail 31; §37.59's operand arrow to `pattern`).
- **The construct's own name.** Read what the construct's clause calls it and match that against each Clause 37 class's definition, not only against the cases the class lists (§16.8 with §37.15 details 1 and 3).
- **A drawn property with no stated value** does not clash with a shall that states the value for the same object (§37.42 against §37.60 detail 1).
- **A closed set without an exact match.** The construct takes the one defined value whose meaning holds for it, and a value outside the normative header is never an option; an integer property in a state no count can express takes vpiUndefined (§12.4.2 for unique0's vpiQualifier; §38.6 and Annex K for vpiDefDecayTime).
- **Rules over items nest.** A rule stated over items applies again to every nested item that fits its terms (§6.24.3's greedy rule inside a dynamic array of strings).
- **An unranked clash.** Read what each clause says it selects, which usually settles the order (§33.4.1.3 to §33.4.1.5 for a cell clause against an inherited liblist).
- **A shall outranks an example and a can** ([shall-outranks-examples-and-can](shall-outranks-examples-and-can.md)).
- **A concern the standard does not raise** does not make a shall optional: the shall is implemented, and the concern, if worth keeping, is filed as its own issue.
- **A choice among conforming implementations** is not a decision for a person: strike every option that breaks a shall and pick from what is left, after reading the clause each constraint is credited to (§23.3.3.7, not §23.3.3.3, permits the inout-port merge).

Once the answer stands, state it per [issues-state-conclusions-not-the-trail](issues-state-conclusions-not-the-trail.md) and remove the label.
