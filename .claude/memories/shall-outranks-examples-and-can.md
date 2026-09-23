---
name: shall-outranks-examples-and-can
description: "In IEEE 1800-2023 a shall is mandatory (§1.5) while examples are informative (§1.10) and can only states possibility; where they clash, the shall decides, without a person"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 0eac2fc8-aa5f-4f95-9fa7-69e4f3f0a42a
  modified: 2026-09-23T02:33:10.422Z
---

# A shall outranks an example and a can

Where IEEE 1800-2023 seems to contradict itself, weigh each side by the kind
of text it is before calling it a decision for a person. §1.5 (printed page
42) makes *shall* a mandatory requirement and *can* a statement of possibility
or capability. §1.10 (printed page 47) makes the code examples informative,
and footnote 7 on printed page 42 says notes carry no requirements. A shall
therefore decides a clash with an example, a note or a can sentence.

**Why:** On 2026-09-22 the user asked whether #2919 and #2920 truly needed a
decision. Both had been labelled 'needs decision' as clashes within the
standard, and §1.5 and §1.10 settled both. In #2919 the §20.4.3 shall on the
precision number's range outranked the example passing 5, so deltahdl was
right. In #2920 the §21.3.4.1 shall on the next `$fgetc` outranked §21.3.4's
can sentence, so deltahdl was wrong.

**How to apply:** Only two requirements of equal force that cannot both hold
go to a person. See [[a-question-the-rules-answer-is-not-a-decision]] and
[[lrm-source-of-truth]].
