// Tests for IEEE 1800-2023 clause 7.9.10 -- associative array arguments.
// Passing an associative array by value creates a local copy of the array in
// the callee. The copy is produced by the simulator's argument-binding path
// (TryBindAssocArg), which duplicates the actual's entries into a fresh formal
// array. Because that behavior depends on how the actual is declared and
// written (clause 7.8, this pass's dependency) and on how the call binds it
// (clause 13.5.1 pass-by-value), every test builds the array from real
// declaration + indexed-assignment source and drives it through
// parse -> elaborate -> lower -> run, observing the value the callee reads and
// the value the caller retains after the call returns.
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// The formal observes the actual's entries: the copy carries every element
// into the callee, so reading a key inside the function returns what the caller
// stored under that key.
TEST(AssocMethods, AssocArgByValueEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  function automatic int read_first(int x[int]);\n"
      "    return x[1];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    aa[1] = 55;\n"
      "    aa[2] = 66;\n"
      "    result = read_first(aa);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 55u);
}

// Because the formal is a local copy, mutating it inside the callee leaves the
// caller's array untouched.
TEST(AssocMethods, AssocArgCallerUnchangedEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int dummy;\n"
      "  int result;\n"
      "  function automatic int mutate(int x[int]);\n"
      "    x[1] = 999;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    aa[1] = 42;\n"
      "    dummy = mutate(aa);\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

// A string-keyed associative array passed by value must reach the callee with
// its entries copied, so the formal observes the actual's value. Exercises the
// production str_data copy in the real argument-binding path.
TEST(AssocMethods, AssocArgStringKeyByValueEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  function automatic int read_key(int x[string]);\n"
      "    return x[\"k\"];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    aa[\"k\"] = 77;\n"
      "    result = read_key(aa);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 77u);
}

// Because the copy is local, mutating a string-keyed formal inside the callee
// leaves the caller's array untouched. Exercises the production binding path
// rather than a hand-written copy.
TEST(AssocMethods, AssocArgStringKeyCallerUnchangedEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[string];\n"
      "  int dummy;\n"
      "  int result;\n"
      "  function automatic int mutate(int x[string]);\n"
      "    x[\"k\"] = 999;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    aa[\"k\"] = 12;\n"
      "    dummy = mutate(aa);\n"
      "    result = aa[\"k\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 12u);
}

// A subroutine argument also appears in a task call. An associative array
// passed by value to a task input is copied into the callee, so the value the
// task reads matches what the caller stored. Exercises the same production
// argument-binding copy through the task-call path, with the read value carried
// back out through a task output.
TEST(AssocMethods, AssocArgByValueThroughTaskEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  task automatic read(input int x[int], output int r);\n"
      "    r = x[1];\n"
      "  endtask\n"
      "  initial begin\n"
      "    aa[1] = 88;\n"
      "    read(aa, result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 88u);
}

}  // namespace
