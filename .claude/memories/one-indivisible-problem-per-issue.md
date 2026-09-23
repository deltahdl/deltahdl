---
name: one-indivisible-problem-per-issue
description: An issue holds exactly one indivisible problem; an issue found holding two is split there and then, one of the halves keeping the number
metadata:
  type: feedback
---

# One indivisible problem per issue

An issue holds one problem and no more: one defect, in one place, with one
fix that closes it. Two defects that share a clause, a failing file list or a
first report are two issues. This holds when filing and when reading: an open
issue found holding two problems is split on the spot, the existing number
kept for the problem its title leads with and the other moved to a new issue,
with the tracker that counts them (#3640 and its like) adjusted to match.

**Why:** An issue with two problems never closes cleanly: it sits open while
half its content is done, its title says less than its body, and nothing in
the tracker says which half is left.

**How to apply:** Ask of each finding whether it could be fixed and closed
alone; where it could, it is its own issue. This applies to every issue
filed, per [[research-lives-in-issues]] or at the user's request, and to any
issue a session brings up to date. Two symptoms of one defect stay
together — a split divides fixes, not file lists.
