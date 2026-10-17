---
name: a-question-the-rules-answer-is-not-a-decision
description: "Before labelling an issue 'needs decision', check whether the standing reminders, the issue or the standards (1800-2023 and 1800.2-2020, and the clauses that cite, parallel or are named by the rule) already answer the question; if one does, act on it"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 51a015a3-4652-42ac-8c15-ce1bc6f6ae12
  modified: 2026-10-17T12:41:06.144Z
---

# A question the rules answer is not a decision

An issue is labelled 'needs decision' only for a question that the autopilot
skill's standing reminders, the issue itself, the linked issues and the
standards all leave open. A question they answer is acted on, with its answer and what
the answer rests on written into the issue.

**Why:** A question the rules already answer has its answer; labelled 'needs
decision', it parks the issue on a person who can only restate that answer.
Questions of order are the usual case: the reminder to solve whatever issues
the original one depends on answers them.

**How to apply:** Before writing a question for a person, test it against each
reminder and against the blocked-by links. For a question of what the language
allows, read the rule in both standards, `~/IEEE 1800-2023.pdf` and
`~/IEEE 1800.2-2020.pdf`, and write what each says into the issue, pages
included; the 2017 edition is no source of truth ([[the-2017-edition]]).
Read beyond the clause itself too: the clause that states the parallel rule
for a sibling construct, and every clause that cites this one, often settle
a reading the clause alone leaves open, as §16.3's grant for immediate
assertions and §17.3's use of the §16.14 list settle that §16.14's list of
places is the whole grant. Read the clauses the rule itself names as well
as those that cite it. When a rule lists constructs that have subclauses
of their own, the list is a summary those subclauses fill in. Read each
listed construct's subclause before weighing readings of the list's
wording. §34.5.27.2 lets a key_block's buffer draw on five pragma
expressions without saying which. But §34.5.10 through §34.5.14 each say
whether their pragma is encrypted into the key_block under a digital
signature, and §34.5.20.2 and §34.5.22.2 show that the list's digest_block
stands for the digest's key, since the digest itself follows the block it
refers to. So a loose and a strict reading of the list were never the
options. Questions of order or priority
between issues the loop selects are answered that way. A concern the
standard does not raise, such as the hazard of loading a library a source
file names under §34.5.28.2, does not make a shall optional: the shall is
implemented and the concern, if worth keeping, is filed as its own issue.
Test the question's premise as well as its options: when it asks how two
of deltahdl's own entities relate, first check that the standard defines
both. If one is only an artifact of the implementation, the standard does
not leave the question open; the question does not arise, and the issue is a
defect. For example, §19.9 loads coverage per covergroup type, so "is a saved
instance the same as the live instance of its name" has no standard answer to
lack. An "implementation-specific" or "left open" sentence covers only what
it names: read every other sentence of the clause and the definition of each
term it uses before calling anything beside it open. §34.5.32.2 makes only a
viewport's access value implementation-specific; its shall that the object be
contained within the envelope, with §34.4's definition of an envelope as a
lexical region, settles that the object name resolves against the envelope's
own declarations, not as an elaborated hierarchical path. For a Clause 37
question of which object a construct is, the diagram and its headline details
are not the whole clause: read every numbered detail through to the end,
examples included. The vpiParent and prefix details often name the object
outright. §37.17 detail 26 and §37.16 detail 31 make a partly indexed packed
select a vpiLogicVar or vpiLogicNet vector, which the object list alone
seemed to leave unnamed. Other diagrams count too: look for every arrow in
Clause 37 that reaches the class in question, not just the arrows drawn in
its own subclause. §37.72 alone seemed to leave open how a struct pattern,
which has one name and one pattern, could stand for a whole `'{a: .x, b: .*}`.
But §37.59 draws an operation's vpiOperand arrow to `pattern`. That makes the
written pattern a vpiAssignmentPatternOp whose operands are the struct
patterns, one per member. A property drawn on a diagram whose value no
detail states does not clash with a shall that states the value for the
same object. §37.42 draws vpiName on every tf call and never says what it
holds. §37.60 detail 1 says that an atomic statement, a call written as a
statement among them, is named by its label or NULL. So an unlabelled call
statement has no name, and only a call inside an expression is named after
its callee. A closed set of values that lacks an exact
match for a construct does not leave the value open: the construct takes the
one defined value whose meaning holds for it, and a value outside the
normative header is never an option. Annex M gives vpiQualifier no unique0
bit, yet §12.4.2 makes unique0 assert the same no-overlap check as unique,
so it reports vpiUniqueQualifier; vpiNoQualifier would deny a check it makes.
A rule stated over "items" applies again to every nested item that fits its
terms. Before calling a nested shape open, apply the rule at each level. §6.24.3's
greedy rule (the first dynamically sized item takes the remainder, and the later
ones stay empty) applies again inside a dynamic array of strings, because each
string is a dynamically sized item. That fixes the shape at one element holding
every remaining byte.
A clash between two rules is not open just because no sentence ranks them.
Read what each clause says it selects, and you can usually settle the order.
In §33.4.1, an instance clause selects only the instance it names
(§33.4.1.3), and that instance's descendants get its liblist by inheritance.
A cell clause selects any instance bound to its cell (§33.4.1.4), and
§33.4.1.5 has the selection clauses choose the current list. So a cell
clause that selects a descendant replaces the list the descendant would
inherit.
A choice of how to implement a rule is not a decision for a person either.
The standard fixes the behaviour, and a person adds nothing by picking among
lowerings that all conform. Strike every option that breaks a shall, then
pick from what is left. Before treating a constraint as a requirement, read
the clause it is credited to. The inout-port merge credited to §23.3.3.3
is in fact §23.3.3.7's permission. §23.3.3.6 confirms that not merging is
allowed, so §32.4.4's interconnect delay on an inout load requires
splitting the port.
Once the answer stands,
state it per [[issues-state-conclusions-not-the-trail]] and remove the label.
