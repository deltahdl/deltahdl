// Tests for IEEE 1800-2023 clause 7.9.6 -- the next() associative array method.
// next() locates the smallest index whose value is strictly greater than the
// given index-argument value; when such an entry exists it assigns that
// successor index to the ref argument and returns 1, otherwise it leaves the
// index unchanged and returns 0. Because "greater" is judged against the value
// currently held in the index variable -- an entry produced by prior indexed
// writes (clause 7.8, this pass's dependency) and handed back through the ref
// argument (clause 13.5.1) -- every test builds the array and its index
// variable from real declaration + indexed-assignment source and drives it
// through parse -> elaborate -> lower -> run, observing either the value next()
// returns or the index it assigns, rather than hand-building the array object.
// The index type is supplied through each dependency's real key syntax:
// integral keys (7.8.4), narrow integral keys, and string keys (7.8.2).

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// Non-empty integral-keyed array with a successor above the current index:
// next() returns 1.
TEST(AssocArrayNextMethod, IntKeyReturnsOneWhenSuccessorExists) {
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
      "    found = aa.first(k);\n"  // k == 10 (smallest)
      "    result = aa.next(k);\n"  // successor of 10 is 30
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// next() assigns the smallest index strictly greater than the current one.
// Starting at the smallest key 10, the successor is 30 (not 50).
TEST(AssocArrayNextMethod, IntKeyAssignsSuccessorIndex) {
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
      "    found = aa.first(k);\n"
      "    found = aa.next(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

// At the largest key there is no successor: next() returns 0.
TEST(AssocArrayNextMethod, IntKeyReturnsZeroAtLargestIndex) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    found = aa.last(k);\n"   // k == 20 (largest)
      "    result = aa.next(k);\n"  // no successor
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// The other half of the failure rule: when next() returns 0 the index variable
// is left unchanged. k is at the largest key 20; after the failed next() it
// must still read 20.
TEST(AssocArrayNextMethod, IntKeyIndexUnchangedWhenNoSuccessor) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    found = aa.last(k);\n"
      "    found = aa.next(k);\n"  // fails, must not touch k
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

// Empty integral-keyed array: next() returns 0.
TEST(AssocArrayNextMethod, IntKeyReturnsZeroWhenEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int result;\n"
      "  initial result = aa.next(k);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// The argument value need not itself be a stored index: next() compares by
// value. k holds 20 (never stored); with keys 10/30/50 the successor is 30.
TEST(AssocArrayNextMethod, IntKeyArgumentNeedNotBeStored) {
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
      "    k = 20;\n"
      "    found = aa.next(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

// A narrow integral index type (dependency 7.8.4) still selects the successor
// by value. Starting at 50 the next stored key is 200.
TEST(AssocArrayNextMethod, NarrowIndexAssignsSuccessor) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[byte unsigned];\n"
      "  byte unsigned ix;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[50] = 1;\n"
      "    aa[200] = 2;\n"
      "    found = aa.first(ix);\n"  // ix == 50
      "    found = aa.next(ix);\n"   // successor is 200
      "    result = ix;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 200u);
}

// String-keyed array (dependency 7.8.2): next() returns 1 when a successor key
// exists lexicographically above the current one.
TEST(AssocArrayNextMethod, StringKeyReturnsOneWhenSuccessorExists) {
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
      "    found = map.first(s);\n"  // s == "apple"
      "    result = map.next(s);\n"  // successor "banana"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// String-keyed next() assigns the lexicographic successor key. Values are
// stored so indexing with the returned key recovers a distinct value: the
// successor of "apple" is "banana", which holds 2.
TEST(AssocArrayNextMethod, StringKeyAssignsSuccessorKey) {
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
      "    found = map.first(s);\n"
      "    found = map.next(s);\n"
      "    result = map[s];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

// At the lexicographically greatest key there is no successor: next() returns
// 0.
TEST(AssocArrayNextMethod, StringKeyReturnsZeroAtGreatestKey) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"apple\"] = 1;\n"
      "    map[\"cherry\"] = 3;\n"
      "    found = map.last(s);\n"   // s == "cherry"
      "    result = map.next(s);\n"  // no successor
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// String argument need not be a stored key. "banana" is never stored but sorts
// between the two stored keys, so next() returns 1 and reaches "cherry".
TEST(AssocArrayNextMethod, StringKeyArgumentNeedNotBeStored) {
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
      "    found = map.next(s);\n"
      "    result = map[s];\n"  // s is now "cherry"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

// The failure rule's "index unchanged" half for the string key type (a distinct
// prod branch from the integral one): at the greatest key next() returns 0 and
// must not disturb the ref string. Observed by indexing with it afterward --
// s must still select the greatest key's value.
TEST(AssocArrayNextMethod, StringKeyIndexUnchangedWhenNoSuccessor) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"apple\"] = 1;\n"
      "    map[\"cherry\"] = 3;\n"
      "    found = map.last(s);\n"  // s == "cherry"
      "    found = map.next(s);\n"  // fails, must leave s == "cherry"
      "    result = map[s];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

// Empty string-keyed array: next() returns 0.
TEST(AssocArrayNextMethod, StringKeyReturnsZeroWhenEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int result;\n"
      "  initial result = map.next(s);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// The clause 7.9.6 worked example: first() seeds the index, then a do/while
// loop drives next() as its condition to walk every entry once. Summing the
// stored value at each visited key proves the full forward traversal and that
// next() terminates by returning 0 past the last key.
TEST(AssocArrayNextMethod, DoWhileTraversalVisitsEveryEntry) {
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
      "    found = map.first(k);\n"
      "    do result = result + map[k];\n"
      "    while (map.next(k));\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 60u);
}

}  // namespace
