---
name: one-point-per-message
description: "Give the user one point or one decision per message, in plain words, saying what each named file, job or script is and whether it exists today or is only proposed."
metadata:
  node_type: memory
  type: feedback
  originSessionId: b425c181-0dc9-4105-9628-ad8462acdd57
  modified: 2026-11-10T05:30:25.027Z
---

# One point per message

Give the user one point, or one decision to make, per message, in a few plain sentences. Say of each thing a message names what it is, and whether it exists today or is only proposed.

**Why:** The user directs the work and does not know every file, CI job and script by name, since sessions wrote most of them. A message that sets out several findings, a table and a list of decisions at once gives the user nothing to act on. One that sets what exists beside what is proposed, without saying which is which, leaves the user unable to tell them apart.

**How to apply:**

- Lead with the answer to what was asked, then stop or give the single next step.
- Hold the other findings until they are asked for, or offer them in one line.
- Say what a file, job or script does before giving its name.
- Ask one question at a time when a decision is the user's, with a recommendation.
