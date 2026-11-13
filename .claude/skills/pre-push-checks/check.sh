#!/bin/bash
set -u

llvm=/opt/homebrew/opt/llvm@22/bin
root=$(git rev-parse --show-toplevel) || exit 1
cd "$root" || exit 1
build=build-check
work=$(mktemp -d)
errors="$work/errors"
: > "$errors"

report() {
  echo "error: $*" | tee -a "$errors"
}

section() {
  echo
  echo "== $*"
}

require_committed() {
  if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
    echo "error: tracked files have uncommitted changes; commit them, then run this again"
    exit 1
  fi
  base=$(git rev-parse "${PRE_PUSH_BASE:-origin/main}") || exit 1
  if [ "$(git rev-list --count "$base..HEAD")" -eq 0 ]; then
    echo "error: HEAD has no commit that ${PRE_PUSH_BASE:-origin/main} lacks"
    exit 1
  fi
  head=$(git rev-parse HEAD) || exit 1
}

check_messages() {
  section "commit messages"
  git log --format='%h' "$base..HEAD" > "$work/commits"
  while read -r sha; do
    subject=$(git log -1 --format=%s "$sha")
    length=${#subject}
    echo "$sha ($length) $subject"
    if [ "$length" -gt 72 ]; then
      report "$sha subject has $length characters, more than 72"
    fi
    git log -1 --format=%B "$sha" | grep -E '^(Closes|Refs|See) #[0-9]+$' | sed 's/^/    /'
  done < "$work/commits"
}

list_files() {
  git diff --name-only --diff-filter=d "$base" HEAD > "$work/files"
  grep -E '\.(cpp|h)$' "$work/files" > "$work/cxx"
  grep -E '^src/.*\.(cpp|h)$' "$work/files" > "$work/src"
  grep -E '^src/.*\.cpp$' "$work/files" > "$work/src_cpp"
  grep -E '^test/src/unit/[^/]+\.cpp$' "$work/files" > "$work/unit"
  sed -e 's|^test/src/unit/||' -e 's|\.cpp$||' "$work/unit" > "$work/targets"
  for extra in "$@"; do
    echo "$extra" >> "$work/targets"
  done
  sort -u -o "$work/targets" "$work/targets"
}

check_format_and_size() {
  section "clang-format and file length"
  while read -r f; do
    "$llvm/clang-format" --dry-run --Werror --style=google "$f" > /dev/null 2>&1 ||
      report "$f is not clang-format --style=google clean"
    lines=$(wc -l < "$f")
    if [ "$f" != src/simulator/vpi_user.h ] && [ "$lines" -gt 1000 ]; then
      report "$f has $lines lines, more than 1000"
    fi
  done < "$work/cxx"
}

check_registration() {
  section "registration and test names"
  while read -r f; do
    name=$(basename "$f" .cpp)
    grep -q "^add_unit_test($name)$" test/CMakeLists.txt ||
      report "$f has no add_unit_test($name) in test/CMakeLists.txt"
    grep -qE '^(TYPED_)?TEST(_[FP])?\(' "$f" || report "$f declares no test"
  done < "$work/unit"
  while read -r f; do
    case "$f" in
      *.cpp) grep -q "${f#src/}" src/CMakeLists.txt ||
        report "$f is not listed in src/CMakeLists.txt" ;;
    esac
  done < "$work/src"
  for f in test/src/unit/*.cpp; do
    tr '\n' ' ' < "$f" |
      grep -oE '(TYPED_)?TEST(_[FP])?\( *[A-Za-z0-9_]+ *, *[A-Za-z0-9_]+ *\)' |
      sed -E 's/^.*\( *([A-Za-z0-9_]+) *, *([A-Za-z0-9_]+) *\)$/\1.\2/'
  done | sort | uniq -d > "$work/duplicates"
  while read -r name; do
    report "test $name is declared more than once"
  done < "$work/duplicates"
}

build_and_test() {
  section "build"
  if [ ! -f "$build/CMakeCache.txt" ]; then
    cmake -B "$build" \
      -DCMAKE_C_COMPILER="$llvm/clang" \
      -DCMAKE_CXX_COMPILER="$llvm/clang++" \
      -DCMAKE_BUILD_TYPE=Debug \
      -DCMAKE_CXX_FLAGS_DEBUG=-g0 \
      "-DCMAKE_CXX_FLAGS=-fprofile-instr-generate -fcoverage-mapping" \
      -DCMAKE_EXE_LINKER_FLAGS=-fprofile-instr-generate > "$work/configure.log" 2>&1 ||
      { tail -40 "$work/configure.log"; report "cmake configure failed"; return 1; }
  fi
  targets=$(tr '\n' ' ' < "$work/targets")
  if ! cmake --build "$build" --parallel 10 --target deltahdl_lib $targets > "$work/build.log" 2>&1; then
    grep -E 'error|Error' "$work/build.log" | head -60
    report "the build failed; the full log is $work/build.log"
    return 1
  fi
  section "unit tests"
  mkdir -p "$work/profiles"
  while read -r t; do
    LLVM_PROFILE_FILE="$work/profiles/$t.profraw" "$build/test/$t" --gtest_brief=1 > "$work/$t.log" 2>&1
    status=$?
    grep -E '^\[(==========|  PASSED  |  FAILED  )\]' "$work/$t.log" | tail -3
    if [ "$status" -ne 0 ]; then
      grep -E '^\[  FAILED  \]|Failure|error:' "$work/$t.log" | head -40
      report "$t failed; the full log is $work/$t.log"
    fi
  done < "$work/targets"
}

changed_lines() {
  git diff -U0 "$base" HEAD -- "$1" |
    sed -nE 's/^@@ -[0-9,]+ \+([0-9]+)(,([0-9]+))? @@.*/\1 \3/p' |
    awk '{ n = ($2 == "") ? 1 : $2; for (i = 0; i < n; i++) print $1 + i }'
}

check_coverage() {
  section "coverage of changed src lines"
  [ -s "$work/src" ] || { echo "no src file changed"; return 0; }
  [ -s "$work/targets" ] || { report "src changed but no unit test ran; name the test targets that reach it as arguments"; return 1; }
  ls "$work"/profiles/*.profraw > /dev/null 2>&1 || { report "no test wrote a profile"; return 1; }
  "$llvm/llvm-profdata" merge -sparse "$work"/profiles/*.profraw -o "$work/merged.profdata" || return 1
  first=""
  objects=""
  while read -r t; do
    if [ -z "$first" ]; then first="$build/test/$t"; else objects="$objects -object $build/test/$t"; fi
  done < "$work/targets"
  files=$(tr '\n' ' ' < "$work/src")
  "$llvm/llvm-cov" export --format=lcov -instr-profile="$work/merged.profdata" \
    "$first" $objects $files > "$work/coverage.lcov" 2> "$work/llvm-cov.log" ||
    { cat "$work/llvm-cov.log"; report "llvm-cov export failed"; return 1; }
  while read -r f; do
    changed_lines "$f" > "$work/changed"
    [ -s "$work/changed" ] || continue
    awk -v file="$root/$f" -v changed="$work/changed" '
      BEGIN { while ((getline l < changed) > 0) want[l] = 1 }
      /^SF:/ { on = (substr($0, 4) == file) }
      on && /^DA:/ { split(substr($0, 4), a, ","); if (a[2] == 0 && want[a[1]]) print "line " a[1] " never ran in the tests that ran" }
      on && /^BRDA:/ { split(substr($0, 6), a, ","); if ((a[4] == "0" || a[4] == "-") && want[a[1]]) print "line " a[1] " has a branch outcome the tests that ran never took" }
    ' "$work/coverage.lcov" | sort -u -t' ' -k2,2n > "$work/missed"
    while read -r miss; do
      report "$f $miss"
    done < "$work/missed"
  done < "$work/src"
}

check_tidy() {
  section "clang-tidy"
  [ -f "$build/compile_commands.json" ] || { report "no compile_commands.json in $build"; return 1; }
  while read -r f; do
    "$llvm/clang-tidy" -p "$build" --quiet --config-file=etc/clang_tidy/src.yml \
      --warnings-as-errors='*' -extra-arg=-w -extra-arg=-ferror-limit=0 "$f" > "$work/tidy.log" 2>&1 ||
      { grep -E 'error:' "$work/tidy.log" | head -40; report "clang-tidy reports $f"; }
  done < "$work/src_cpp"
  while read -r f; do
    "$llvm/clang-tidy" -p "$build" --quiet --config-file=etc/clang_tidy/test_src_unit.yml \
      --warnings-as-errors='*' -extra-arg=-w -extra-arg=-ferror-limit=0 "$f" > "$work/tidy.log" 2>&1 ||
      { grep -E 'error:' "$work/tidy.log" | head -40; report "clang-tidy reports $f"; }
  done < "$work/unit"
}

check_unchanged() {
  section "working tree"
  if [ "$(git rev-parse HEAD)" != "$head" ] ||
    [ -n "$(git status --porcelain --untracked-files=no)" ]; then
    report "HEAD or a tracked file changed while the checks ran, so they checked something other than the commit; leave the tree alone and run this again"
    return 1
  fi
  echo "HEAD and the tracked files are as they were at the start"
}

require_committed
list_files "$@"
check_messages
check_format_and_size
check_registration
build_and_test && check_coverage
check_tidy
check_unchanged

section "result"
if [ -s "$errors" ]; then
  echo "$(wc -l < "$errors" | tr -d ' ') problem(s); fix them, amend or add a commit, and run this again:"
  cat "$errors"
  exit 1
fi
echo "every check passed; push"
