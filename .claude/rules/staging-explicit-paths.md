# Staging explicit paths

Never use `git add -A` or `git add .`. Stage each file by its path.

`.gitignore` excludes `.claude/scheduled_tasks.lock` and not the rest of `.claude/`, which carries these notes and `.claude/skills/`, so a `git add -A` there stages a session's lock file alongside them. Other untracked scratch appears from time to time as well, so explicit staging is the rule regardless.

Name a removed path to `git rm` and an added or modified path to `git add`, and never name both kinds to one command. `git add` stages none of its pathspecs when any one of them matches nothing on disk: it reports `fatal: pathspec '<path>' did not match any files` and returns non-zero, having staged nothing at all rather than everything but the bad path. A rename is what produces such a list, because the old path is gone from disk while the new one is not yet tracked, so a session listing every path a rename touched hits this on the first try.

Read the index back with `git status --porcelain` after staging and before committing, and compare what it lists against what the change touched. A failed staging command returns non-zero, and that decides nothing when `git add` and `git commit` are separate lines rather than one `&&` chain, because nothing reads the exit status. Reading the index is what makes the failure visible whatever caused it, and it costs one command.

Related: [git-add-all-swept-scratch](../memories/git-add-all-swept-scratch.md) and [git-add-partial-staging](../memories/git-add-partial-staging.md) for what each of those has cost.
