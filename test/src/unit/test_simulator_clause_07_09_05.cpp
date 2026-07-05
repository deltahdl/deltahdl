// Tests for IEEE 1800-2023 clause 7.9.5 -- the last() associative array method.
// last() assigns to its ref index argument the largest index present in the
// array and returns 1; on an empty array it returns 0 and leaves the index
// unchanged. Which index is "largest" is determined by the entries produced by
// prior indexed writes (clause 7.8, this pass's dependency), so every test
// builds the array from real declaration + indexed-assignment source and drives
// it through parse -> elaborate -> lower -> run, observing either the value
// last() returns or the index it assigns, rather than hand-building the array
// object. The index type is supplied through each dependency's real key syntax:
// integral keys (7.8.4) and string keys (7.8.2).

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// Non-empty integral-keyed array: last() returns 1.
TEST(AssocArrayLastMethod, IntKeyReturnsOneWhenNonEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[30] = 300;\n"
      "    aa[20] = 200;\n"
      "    result = aa.last(k);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// last() assigns the largest (greatest) index, regardless of insertion order.
// Keys are written 10, 30, 20; the assigned index must be 30.
TEST(AssocArrayLastMethod, IntKeyAssignsLargestIndex) {
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
      "    found = aa.last(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

// Empty integral-keyed array: last() returns 0.
TEST(AssocArrayLastMethod, IntKeyReturnsZeroWhenEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int result;\n"
      "  initial result = aa.last(k);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// A narrow integral index type (dependency 7.8.4) still selects the largest
// stored key. Keys 50 and 200 are written; last() picks 200.
TEST(AssocArrayLastMethod, NarrowIndexAssignsLargestIndex) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[byte unsigned];\n"
      "  byte unsigned ix;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[50] = 1;\n"
      "    aa[200] = 2;\n"
      "    found = aa.last(ix);\n"
      "    result = ix;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 200u);
}

// String-keyed array (dependency 7.8.2): last() returns 1 when non-empty.
TEST(AssocArrayLastMethod, StringKeyReturnsOneWhenNonEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"apple\"] = 1;\n"
      "    map[\"cherry\"] = 3;\n"
      "    result = map.last(s);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// String-keyed last() selects the lexicographically greatest key. Values are
// stored so that indexing with the returned key recovers a distinct value:
// keys apple/banana/cherry hold 1/2/3, so last() -> "cherry" and map[s] == 3.
TEST(AssocArrayLastMethod, StringKeyAssignsGreatestKey) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"apple\"] = 1;\n"
      "    map[\"banana\"] = 2;\n"
      "    map[\"cherry\"] = 3;\n"
      "    found = map.last(s);\n"
      "    result = map[s];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

// Empty string-keyed array: last() returns 0.
TEST(AssocArrayLastMethod, StringKeyReturnsZeroWhenEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int result;\n"
      "  initial result = map.last(s);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// The clause 7.9.5 worked example: because the array is non-empty, last() is
// true and the guarded statement runs. Here the then-branch records that the
// greatest key was reached.
TEST(AssocArrayLastMethod, IfConditionTakesBranchWhenNonEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    map[\"x\"] = 9;\n"
      "    if (map.last(s))\n"
      "      result = map[s];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

}  // namespace
