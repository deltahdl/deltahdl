// Tests for IEEE 1800-2023 clause 7.9.4 -- the first() associative array
// method. first() assigns to its ref index argument the smallest index present
// in the array and returns 1; on an empty array it returns 0 and leaves the
// index unchanged. Which index is "smallest" is determined by the entries
// produced by prior indexed writes (clause 7.8, this pass's dependency), and
// the index is delivered back to the caller through the ref argument
// (clause 13.5.1), so every test builds the array from real declaration +
// indexed-assignment source and drives it through parse -> elaborate -> lower
// -> run, observing either the value first() returns or the index it assigns,
// rather than hand-building the array object. The index type is supplied
// through each dependency's real key syntax: integral keys (7.8.4) and string
// keys (7.8.2).

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// Non-empty integral-keyed array: first() returns 1.
TEST(AssocArrayFirstMethod, IntKeyReturnsOneWhenNonEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[30] = 300;\n"
      "    aa[20] = 200;\n"
      "    result = aa.first(k);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// first() assigns the smallest (least) index, regardless of insertion order.
// Keys are written 10, 30, 20; the assigned index must be 10.
TEST(AssocArrayFirstMethod, IntKeyAssignsSmallestIndex) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[30] = 300;\n"
      "    aa[20] = 200;\n"
      "    found = aa.first(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 10u);
}

// Empty integral-keyed array: first() returns 0.
TEST(AssocArrayFirstMethod, IntKeyReturnsZeroWhenEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int result;\n"
      "  initial result = aa.first(k);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// A narrow integral index type (dependency 7.8.4) still selects the smallest
// stored key. Keys 50 and 200 are written; first() picks 50.
TEST(AssocArrayFirstMethod, NarrowIndexAssignsSmallestIndex) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[byte unsigned];\n"
      "  byte unsigned ix;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[50] = 1;\n"
      "    aa[200] = 2;\n"
      "    found = aa.first(ix);\n"
      "    result = ix;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 50u);
}

// String-keyed array (dependency 7.8.2): first() returns 1 when non-empty.
TEST(AssocArrayFirstMethod, StringKeyReturnsOneWhenNonEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"apple\"] = 1;\n"
      "    map[\"cherry\"] = 3;\n"
      "    result = map.first(s);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// String-keyed first() selects the lexicographically smallest key. Values are
// stored so that indexing with the returned key recovers a distinct value:
// keys apple/banana/cherry hold 1/2/3, so first() -> "apple" and map[s] == 1.
TEST(AssocArrayFirstMethod, StringKeyAssignsSmallestKey) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"cherry\"] = 3;\n"
      "    map[\"apple\"] = 1;\n"
      "    map[\"banana\"] = 2;\n"
      "    found = map.first(s);\n"
      "    result = map[s];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// Empty string-keyed array: first() returns 0.
TEST(AssocArrayFirstMethod, StringKeyReturnsZeroWhenEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int result;\n"
      "  initial result = map.first(s);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// The clause 7.9.4 worked example: because the array is non-empty, first() is
// true and the guarded statement runs. Here the then-branch records the value
// stored under the smallest key that first() reached.
TEST(AssocArrayFirstMethod, IfConditionTakesBranchWhenNonEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    map[\"x\"] = 9;\n"
      "    if (map.first(s))\n"
      "      result = map[s];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

}  // namespace
