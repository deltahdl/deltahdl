---
name: shall-outranks-examples-and-can
description: "In IEEE 1800-2023 a shall is mandatory (§1.5) while examples are informative (§1.10) and can only states possibility; where they clash, the shall decides, without a person"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 68e93dca-df8f-4fa9-a625-c13a34fbd398
  modified: 2026-10-15T23:04:03.874Z
---

# A shall outranks an example and a can

Where IEEE 1800-2023 seems to contradict itself, weigh each side by the kind
of text it is before calling it a decision for a person. §1.5 (printed page
42) makes *shall* a mandatory requirement and *can* a statement of possibility
or capability. §1.10 (printed page 47) makes the code examples informative,
and footnote 7 on printed page 42 says notes carry no requirements. A shall
therefore decides a clash with an example, a note or a can sentence.

**Why:** §1.5 and §1.10 settle such a clash from within the standard, so it
is not a question for a person. It cuts both ways: the §20.4.3 shall on the
precision number's range outranks the clause's example passing 5, and the
§21.3.4.1 shall on the next `$fgetc` outranks §21.3.4's can sentence.

**How to apply:** Only two requirements of equal force that cannot both hold
go to a person. Two shalls are not equal when one is written for the exact
case and the other is general. Ask what each would leave the other to
govern. If letting the general rule govern would leave the specific shall
nothing to apply to, the specific one governs. §33.3.1.1 requires a warning
for same-named modules mapped into one library in one invocation. Every
file lands in some library, so a §3.13(a) error there would leave that
warning nothing to apply to. See [[a-question-the-rules-answer-is-not-a-decision]] and
[[lrm-source-of-truth]].
