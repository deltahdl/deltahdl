---
name: long-running-commands-in-the-background
description: "Run any command that can take more than about a minute, a CI watch included, with `run_in_background: true` and end the turn, so scheduled reminders can fire while it runs; never wait in the foreground, and watch a run with `--interval 60`."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 27e0be22-8d03-49f3-9685-98b0b82cf6ca
  modified: 2026-09-29T13:43:29.371Z
---

# Long-running commands in the background

Run every command that can take more than about a minute as a background Bash call (`run_in_background: true`), then end the turn and let its completion notification resume the work. This covers a sweep of `gh` calls over many issues and a long `grep` or `find` over the tree, as well as the wait for a CI run. So do a local build, a test run and the `pre-push-checks` skill ([verifying-through-ci](verifying-through-ci.md)), whose first build of the library takes several minutes.

**Why:** The autopilot's reminders are cron jobs, and a cron job fires only while the session is idle between turns. A foreground command holds the turn for as long as it runs, so every reminder due in that time waits behind it, and the user cannot type either. A background command frees the turn as soon as it starts.

**How to apply:**

- Give a command that might not end a time limit as well, such as `perl -e 'alarm 60; exec @ARGV' <command>`; macOS has no `timeout` command.
- Send the output to a file under the scratchpad, and read that file once the notification arrives.
- Never follow a background command with a foreground wait: no `sleep`, no `until` loop, and no rereading of its output file until it fills. Any of these blocks the session again.
- While it runs, do nothing but wait, per [waiting-while-anything-runs-in-the-background](waiting-while-anything-runs-in-the-background.md): it is the last call of its turn, and the work resumes on its notification.
- A turn made of many short foreground calls also holds the reminders back until it ends. Split long work at its natural boundaries, such as after a build starts or after a batch of edits, rather than running it all in one turn.

## Watching a CI run

- Start `gh run watch <id> --interval 60 --exit-status` as a background Bash command, or use the Monitor tool, and let the notification bring the result; then read the run as [reading-a-ci-run](reading-a-ci-run.md) says. Find the run's id as [gh-run-list-commit-takes-a-full-sha](gh-run-list-commit-takes-a-full-sha.md) says.
- Never run `gh run watch` in the foreground: it holds the whole session for the length of the run.
- Always pass `--interval 60`. The default polls every 3 seconds, and over a run of most of an hour that tripped GitHub's secondary rate limit: every `gh` call came back HTTP 403 while `gh api rate_limit` still showed every bucket full, and it clears only after minutes of quiet. When it trips, wait in a background `sleep` before the next `gh` call rather than retrying.
