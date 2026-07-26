# Not harvesting a running workflow's worktrees

Do not copy out and `git worktree remove` a workflow's isolated worktrees
until its completion notification actually arrives. Mid-run, `git worktree
list` and per-worktree `git status` can look finished when they are not.

On 2026-06-20 a session was resumed, all thirteen `wf_*` worktrees were
present with uncommitted changes, the header-surgery workflow was assumed
finished, the changes were copied into main as commit `1ce66a18b`, and all
thirteen worktrees were force-removed. The user's interface still showed
"12/13 agents done". The thirteenth agent's worktree was torn down
mid-edit. It happened to have finished its real work and to be writing its
report, so nothing was lost, but it could as easily have been a partial
capture.

Wait for the completion notification — a background workflow re-invokes on
completion, so there is nothing to pre-empt. A `locked` worktree in
`git worktree list` is a strong signal that its agent is still active, and
should never be force-removed as cleanup. If mid-run inspection is
necessary, read only. Worktrees sitting at the base commit with
uncommitted changes is normal for in-flight and finished agents alike, and
proves nothing either way.
