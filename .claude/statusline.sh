#!/bin/bash
# Claude Code status line: tokens in context, the weekly usage bar, and the repo's open issue count.

input=$(cat)
# The tokens in context now: the last request's input, cache writes and cache
# reads, or the used share of the window where no request has reported yet.
ctx=$(echo "$input" | jq -r '.context_window as $w
  | if $w.current_usage then
      ($w.current_usage | (.input_tokens // 0) + (.cache_creation_input_tokens // 0) + (.cache_read_input_tokens // 0))
    elif $w.used_percentage and $w.context_window_size then
      $w.used_percentage * $w.context_window_size / 100
    else empty end')
wk=$(echo "$input" | jq -r '.rate_limits.seven_day.used_percentage // empty')
cwd=$(echo "$input" | jq -r '.workspace.current_dir // .cwd // empty')

full=$(printf '\342\226\210')
empty=$(printf '\342\226\221')

bar() {
  local n f b i
  n=$(printf '%.0f' "$2")
  f=$((n / 10))
  [ "$f" -gt 10 ] && f=10
  [ "$f" -lt 0 ] && f=0
  b=''
  for ((i = 1; i <= 10; i++)); do
    if [ "$i" -le "$f" ]; then b="${b}${full}"; else b="${b}${empty}"; fi
  done
  printf '%s %s %s%%' "$1" "$b" "$n"
}

out=''
[ -n "$ctx" ] && out=$(printf 'Context %.0fK' "$(echo "$ctx / 1000" | bc -l)")
[ -n "$wk" ] && out="${out}${out:+  |  }$(bar Weekly "$wk")"

# gh is slow, so the count is cached per working directory for two minutes.
if [ -n "$cwd" ]; then
  cache="${TMPDIR:-/tmp}/claude-statusline-issues-$(printf '%s' "$cwd" | cksum | cut -d' ' -f1)"
  if [ ! -s "$cache" ] || [ -n "$(find "$cache" -mmin +2 2>/dev/null)" ]; then
    count=$(cd "$cwd" 2>/dev/null && GH_PROMPT_DISABLED=1 gh repo view --json issues -q .issues.totalCount 2>/dev/null)
    [ -n "$count" ] && printf '%s' "$count" > "$cache"
  fi
  issues=$(cat "$cache" 2>/dev/null)
  [ -n "$issues" ] && out="${out}${out:+  |  }Open issues: $issues"
fi

printf '%s' "$out"
