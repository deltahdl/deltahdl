// Tests for IEEE 1800-2023 clause 7.9.7 -- the prev() associative array method.
// prev() locates the largest index whose value is strictly smaller than the
// given index-argument value; when such an entry exists it assigns that
// predecessor index to the ref argument and returns 1, otherwise it leaves the
// index unchanged and returns 0. Because "smaller" is judged against the value
// currently held in the index variable -- an entry produced by prior indexed
// writes (clause 7.8, this pass's dependency) and handed back through the ref
// argument (clause 13.5.1) -- every test builds the array and its index
// variable from real declaration + indexed-assignment source and drives it
// through parse -> elaborate -> lower -> run, observing either the value prev()
// returns or the index it assigns, rather than hand-building the array object.
// The index type is supplied through each dependency's real key syntax:
// integral keys, narrow integral keys, and string keys. prev() is the reverse
// polarity of next() (clause 7.9.6); the two share one production path.

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// Non-empty integral-keyed array with a predecessor below the current index:
// prev() returns 1.
TEST(AssocArrayPrevMethod, IntKeyReturnsOneWhenPredecessorExists) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[30] = 300;\n"
      "    aa[50] = 500;\n"
      "    found = aa.last(k);\n"   // k == 50 (largest)
      "    result = aa.prev(k);\n"  // predecessor of 50 is 30
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// prev() assigns the largest index strictly smaller than the current one.
// Starting at the largest key 50, the predecessor is 30 (not 10).
TEST(AssocArrayPrevMethod, IntKeyAssignsPredecessorIndex) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[30] = 300;\n"
      "    aa[50] = 500;\n"
      "    found = aa.last(k);\n"
      "    found = aa.prev(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

// At the smallest key there is no predecessor: prev() returns 0.
TEST(AssocArrayPrevMethod, IntKeyReturnsZeroAtSmallestIndex) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    found = aa.first(k);\n"  // k == 10 (smallest)
      "    result = aa.prev(k);\n"  // no predecessor
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// The other half of the failure rule: when prev() returns 0 the index variable
// is left unchanged. k is at the smallest key 10; after the failed prev() it
// must still read 10.
TEST(AssocArrayPrevMethod, IntKeyIndexUnchangedWhenNoPredecessor) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    found = aa.first(k);\n"
      "    found = aa.prev(k);\n"  // fails, must not touch k
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 10u);
}

// Empty integral-keyed array: prev() returns 0.
TEST(AssocArrayPrevMethod, IntKeyReturnsZeroWhenEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int result;\n"
      "  initial result = aa.prev(k);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// The argument value need not itself be a stored index: prev() compares by
// value. k holds 40 (never stored); with keys 10/30/50 the predecessor is 30.
TEST(AssocArrayPrevMethod, IntKeyArgumentNeedNotBeStored) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[30] = 300;\n"
      "    aa[50] = 500;\n"
      "    k = 40;\n"
      "    found = aa.prev(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

// When the argument value exceeds every stored index, the largest stored index
// is still strictly smaller than it, so prev() reaches that last key. k holds
// 100 (never stored); the predecessor is 30.
TEST(AssocArrayPrevMethod, IntKeyArgumentAboveAllKeysReachesLast) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    aa[30] = 300;\n"
      "    k = 100;\n"
      "    found = aa.prev(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

// A narrow integral index type still selects the predecessor by value. Starting
// at 200 the previous stored key is 50.
TEST(AssocArrayPrevMethod, NarrowIndexAssignsPredecessor) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[byte unsigned];\n"
      "  byte unsigned ix;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[50] = 1;\n"
      "    aa[200] = 2;\n"
      "    found = aa.last(ix);\n"  // ix == 200
      "    found = aa.prev(ix);\n"  // predecessor is 50
      "    result = ix;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 50u);
}

// String-keyed array: prev() returns 1 when a predecessor key exists
// lexicographically below the current one.
TEST(AssocArrayPrevMethod, StringKeyReturnsOneWhenPredecessorExists) {
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
      "    found = map.last(s);\n"   // s == "cherry"
      "    result = map.prev(s);\n"  // predecessor "banana"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// String-keyed prev() assigns the lexicographic predecessor key. Values are
// stored so indexing with the returned key recovers a distinct value: the
// predecessor of "cherry" is "banana", which holds 2.
TEST(AssocArrayPrevMethod, StringKeyAssignsPredecessorKey) {
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
      "    found = map.prev(s);\n"
      "    result = map[s];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

// At the lexicographically smallest key there is no predecessor: prev() returns
// 0.
TEST(AssocArrayPrevMethod, StringKeyReturnsZeroAtSmallestKey) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"apple\"] = 1;\n"
      "    map[\"cherry\"] = 3;\n"
      "    found = map.first(s);\n"  // s == "apple"
      "    result = map.prev(s);\n"  // no predecessor
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// String argument need not be a stored key. "banana" is never stored but sorts
// between the two stored keys, so prev() returns 1 and reaches "apple".
TEST(AssocArrayPrevMethod, StringKeyArgumentNeedNotBeStored) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"apple\"] = 1;\n"
      "    map[\"cherry\"] = 3;\n"
      "    s = \"banana\";\n"
      "    found = map.prev(s);\n"
      "    result = map[s];\n"  // s is now "apple"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// The failure rule's "index unchanged" half for the string key type (a distinct
// prod branch from the integral one): at the smallest key prev() returns 0 and
// must not disturb the ref string. Observed by indexing with it afterward --
// s must still select the smallest key's value.
TEST(AssocArrayPrevMethod, StringKeyIndexUnchangedWhenNoPredecessor) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"apple\"] = 1;\n"
      "    map[\"cherry\"] = 3;\n"
      "    found = map.first(s);\n"  // s == "apple"
      "    found = map.prev(s);\n"   // fails, must leave s == "apple"
      "    result = map[s];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// Empty string-keyed array: prev() returns 0.
TEST(AssocArrayPrevMethod, StringKeyReturnsZeroWhenEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int result;\n"
      "  initial result = map.prev(s);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// The clause 7.9.7 worked example: last() seeds the index, then a do/while loop
// drives prev() as its condition to walk every entry once in reverse. Summing
// the stored value at each visited key proves the full backward traversal and
// that prev() terminates by returning 0 past the first key.
TEST(AssocArrayPrevMethod, DoWhileReverseTraversalVisitsEveryEntry) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[1] = 10;\n"
      "    map[2] = 20;\n"
      "    map[3] = 30;\n"
      "    result = 0;\n"
      "    found = map.last(k);\n"
      "    do result = result + map[k];\n"
      "    while (map.prev(k));\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 60u);
}

}  // namespace
