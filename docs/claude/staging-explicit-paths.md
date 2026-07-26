# Staging explicit paths

Never use `git add -A` or `git add .`. Stage each file by its path.

The working tree carries untracked scratch directories. One `git add -A`
swept about 112,000 lines of them into commit `9df98e152`, which the user
caught. Recovering meant `git rm -r --cached`, a `.gitignore` entry, an
amend, and a force-push with lease to scrub it from history.

`.claude/` is in `.gitignore` now, but other untracked scratch appears
from time to time, so explicit staging is the rule regardless.
