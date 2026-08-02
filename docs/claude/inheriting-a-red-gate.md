# Inheriting a red gate

Fix a red run in the session that finds it, whoever caused it, and fix it before the session's own work counts as verified.

A gate that scans the whole tree rather than the diff indicts whoever pushes next, and that is the design rather than a flaw in it. The tree is held clean collectively. A file over a limit, a file the formatter would rewrite, a registration that was never added — each is the next pusher's to fix, whether or not their change went near it. Putting such a gate in front of the build is what makes the fix non-optional. Take it as the standing instruction it is: the gate has already decided the work is not done, and declining it because the breach came from elsewhere leaves the tree dirty for the next session to decline in turn.

Do not read a run's conclusion as a verdict on the change that triggered it. `gh run list` reports `failure` identically whether the push broke something or inherited a break, and a skipped job reports neither pass nor fail. A session that reads the conclusion alone therefore learns nothing about its own change in either case. `gh run view --log-failed` is what separates them. A pre-existing failure is a task, not a disposition.

One run tells you how much there is to take on. A job stops at its first failing step, so a job holding several whole-tree scans used to report the earliest breach and nothing about the rest: the backlog behind it appeared only once that breach was cleared, and a session sizing the work up beforehand was systematically wrong. Each scanning step now runs whatever the steps ahead of it found, so a single red run names every breach at once. Nothing is un-gated by that, because any one of them still fails the job.

The damage compounds instead of correcting itself. When the failing gate is upstream of the jobs that build and test, every one of them is skipped, so the change ships with nothing observed. Each session that reads the red as somebody else's adds another commit whose tests never ran, and the next session sees the same red and reaches the same conclusion. Nothing in the signal degrades as the pile grows: the fiftieth run looks exactly like the first.

Recorded on 2026-08-01, after a header crossed the line cap and fifty-four commits touching `src/` or `test/` landed behind it, none of them compiled or tested. Every one of those pushes was told `failure`, and every one of them read it as the failure that was already there.
