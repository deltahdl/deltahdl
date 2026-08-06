// Tests for IEEE 1800-2023 clause 7.12.4 -- iterator index querying. The
// expressions used by an array manipulation method may need the array index at
// each iteration, not just the element. The index method of the iterator
// (spelled `item.index` by default) returns the index value of the current
// iteration. Because that value only exists while a real array manipulation
// method iterates a real array, every test builds the array from a real
// declaration + initializer (dynamic array of 7.5, fixed array of 7.4, or
// associative array of 7.8) and drives `arr.method with (... item.index ...)`
// through parse -> elaborate -> lower -> run, observing the queue/array the
// method returns rather than hand-building the iterator scope. The dependency
// clauses supply the input: 20.7 numbers the dimensions the index method
// reports, and 7.8/7.8.1 supply the associative index type whose value the
// index method returns for an associative array.

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §7.12.4 -- the default index method name `index` reports the 0-based position
// of each element. find with (item.index > 0) keeps the elements at positions 1
// and 2, so the first survivor is the element at position 1 (200).
TEST(ArrayIteratorIndex, DefaultIndexSelectsByPositionInFind) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int arr[] = {100, 200, 300};\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    found = arr.find with (item.index > 0);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 200u);
}

// §7.12.4 -- find_index over the same index predicate returns the positions
// themselves; the second qualifying position is 2.
TEST(ArrayIteratorIndex, DefaultIndexInFindIndex) {
  uint64_t p = RunAndGet(
      "module m;\n"
      "  int arr[] = {100, 200, 300};\n"
      "  int idx[$];\n"
      "  int p;\n"
      "  initial begin\n"
      "    idx = arr.find_index with (item.index > 0);\n"
      "    p = idx[1];\n"
      "  end\n"
      "endmodule\n",
      "p");
  EXPECT_EQ(p, 2u);
}

// §7.12.4 -- find_first keeps the first element whose position satisfies the
// index predicate; index >= 2 first holds at position 2 (element 15).
TEST(ArrayIteratorIndex, DefaultIndexInFindFirst) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int arr[] = {5, 10, 15, 20};\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    found = arr.find_first with (item.index >= 2);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 15u);
}

// §7.12.4 -- find_last keeps the last element whose position satisfies the
// index predicate; index < 2 last holds at position 1 (element 10).
TEST(ArrayIteratorIndex, DefaultIndexInFindLast) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int arr[] = {5, 10, 15, 20};\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    found = arr.find_last with (item.index < 2);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 10u);
}

// §7.12.4 -- find_first_index returns the position of the first qualifying
// element; index > 1 first holds at position 2.
TEST(ArrayIteratorIndex, DefaultIndexInFindFirstIndex) {
  uint64_t p = RunAndGet(
      "module m;\n"
      "  int arr[] = {5, 10, 15, 20};\n"
      "  int idx[$];\n"
      "  int p;\n"
      "  initial begin\n"
      "    idx = arr.find_first_index with (item.index > 1);\n"
      "    p = idx[0];\n"
      "  end\n"
      "endmodule\n",
      "p");
  EXPECT_EQ(p, 2u);
}

// §7.12.4 -- find_last_index returns the position of the last qualifying
// element; index < 3 last holds at position 2.
TEST(ArrayIteratorIndex, DefaultIndexInFindLastIndex) {
  uint64_t p = RunAndGet(
      "module m;\n"
      "  int arr[] = {5, 10, 15, 20};\n"
      "  int idx[$];\n"
      "  int p;\n"
      "  initial begin\n"
      "    idx = arr.find_last_index with (item.index < 3);\n"
      "    p = idx[0];\n"
      "  end\n"
      "endmodule\n",
      "p");
  EXPECT_EQ(p, 2u);
}

// §7.12.4 -- the index method reads alongside the element in the same
// predicate. find with (item == item.index) keeps elements equal to their own
// position: element 1 sits at position 1 and element 2 at position 2, so both
// survive while the leading 2 (position 0) and trailing 9 do not.
TEST(ArrayIteratorIndex, IndexComparedToElementValue) {
  uint64_t sz = RunAndGet(
      "module m;\n"
      "  int arr[] = {2, 1, 2, 9};\n"
      "  int found[$];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    found = arr.find with (item == item.index);\n"
      "    sz = found.size();\n"
      "  end\n"
      "endmodule\n",
      "sz");
  EXPECT_EQ(sz, 2u);
}

// §7.12.4 -- the index method reports the same 0-based positions when the
// iterated array is a fixed-size unpacked array (§7.4) rather than a dynamic
// one; index >= 1 keeps positions 1 and 2 (elements 20 and 30).
TEST(ArrayIteratorIndex, DefaultIndexOverFixedArray) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  logic [7:0] a [0:2] = '{8'd10, 8'd20, 8'd30};\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    found = a.find with (item.index >= 1);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 20u);
}

// §7.12.4 -- the return type of the index method is a 32-bit int for a
// non-associative array. Multiplying the index by 1000 in a find predicate over
// the largest position (2) selects the last element, confirming the index
// arithmetic runs at full int width rather than truncating.
TEST(ArrayIteratorIndex, IndexIsIntForNonAssociative) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int arr[] = {42, 99, 7};\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    found = arr.find with (item.index * 1000 >= 2000);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 7u);
}

// §7.12.4 -- for an associative array the index method returns a value of the
// associative index type (§7.8), i.e. the key, not a 0-based position. Here the
// integer key 20 is matched, selecting the value 200 stored under it.
TEST(ArrayIteratorIndex, AssociativeIndexReturnsKey) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int aa[int];\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    aa[30] = 300;\n"
      "    found = aa.find with (item.index == 20);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 200u);
}

// §7.12.4 -- when the default name `index` would clash, the optional index
// argument of the array method renames the iterator index. arr.find(elem, pos)
// binds the element to `elem` and the index method to `pos`, so elem.pos reads
// the position; pos < 2 keeps positions 0 and 1 (elements 10 and 20).
TEST(ArrayIteratorIndex, RenamedIndexArgumentInFind) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int arr[] = {10, 20, 30, 40};\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    found = arr.find(elem, pos) with (elem.pos < 2);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 10u);
}

// §7.12.4 -- the renamed index works with a renamed element name too:
// find_index(x, i) with (x.i > 0) returns the positions of the last two
// elements; the second qualifying position is 2.
TEST(ArrayIteratorIndex, RenamedIndexArgumentInFindIndex) {
  uint64_t p = RunAndGet(
      "module m;\n"
      "  int arr[] = {100, 200, 300};\n"
      "  int idx[$];\n"
      "  int p;\n"
      "  initial begin\n"
      "    idx = arr.find_index(x, i) with (x.i > 0);\n"
      "    p = idx[1];\n"
      "  end\n"
      "endmodule\n",
      "p");
  EXPECT_EQ(p, 2u);
}

// §7.12.4 -- an empty array never binds an index, so an index predicate keeps
// nothing.
TEST(ArrayIteratorIndex, EmptyArrayIndexKeepsNothing) {
  uint64_t sz = RunAndGet(
      "module m;\n"
      "  int arr[];\n"
      "  int found[$];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    found = arr.find with (item.index >= 0);\n"
      "    sz = found.size();\n"
      "  end\n"
      "endmodule\n",
      "sz");
  EXPECT_EQ(sz, 0u);
}

// §7.12.4 -- a single-element array binds only index 0.
TEST(ArrayIteratorIndex, SingleElementIndexIsZero) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int arr[] = {77};\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    found = arr.find with (item.index == 0);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 77u);
}

// §7.12.4 -- the index method reports positions when the iterated array is a
// queue (§7.10) rather than a dynamic or fixed array; the queue is a distinct
// unpacked-array kind with its own element-collection path. Built from a real
// queue initializer, index >= 2 keeps positions 2 and 3 (elements 25 and 35),
// so the first survivor is 25.
TEST(ArrayIteratorIndex, IndexOverQueue) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int q [$] = {5, 15, 25, 35};\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    found = q.find with (item.index >= 2);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 25u);
}

// §7.12.4 -- the index method is available in a reduction method's with clause
// too, not only the locator family. This exercises the reduction iteration path
// (a distinct binding site from the locator path) applying the same index
// method. Summing the positions of a three-element array yields 0+1+2 == 3.
TEST(ArrayIteratorIndex, IndexInReductionMethod) {
  uint64_t r = RunAndGet(
      "module m;\n"
      "  int arr[] = {50, 60, 70};\n"
      "  int r;\n"
      "  initial r = arr.sum() with (item.index);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(r, 3u);
}

}  // namespace
