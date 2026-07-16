// Tests for IEEE 1800-2023 clause 7.12.5 -- the array map() method. map()
// returns an unpacked array with the same range (or, for an associative array,
// the same set of index values) as the source, with each element replaced by
// the value of the required with expression. Three rules are enumerated here:
//   (1) each element is replaced by the with value, and that with clause is
//       required (a bare map() is illegal);
//   (2) each returned element takes the self-determined type of the with
//       expression (dependency 11.6.1 supplies that type);
//   (3) the returned range / set of index values and index type match the
//       source.
// map()'s result depends on how the source array is produced -- its element
// type, its array kind (fixed 7.4, dynamic 7.5, queue 7.10, or associative
// 7.8), and its index type -- so every test builds the source from a real
// declaration + initializer and drives `dst = src.map() with (...)` through
// parse -> elaborate -> lower -> run, observing the array/queue the method
// produces rather than hand-building the iterator scope.

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// Runs a full-pipeline design and reports whether the simulation raised a
// diagnostic. Used for the with-clause-required rule, whose violation is
// detected while the map method executes (not at elaboration), so the design
// must actually run before the error appears.
bool RunProducesError(const std::string& src) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  if (!design) return true;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  return f.diag.HasErrors();
}

// Runs a full-pipeline design and returns the width of element `idx` of queue
// `qname` after the run, so the self-determined element type of a map result
// can be observed directly rather than inferred from a value.
uint32_t RunQueueElemWidth(const std::string& src, const char* qname,
                           size_t idx) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  auto* q = f.ctx.FindQueue(qname);
  EXPECT_NE(q, nullptr);
  if (!q || idx >= q->elements.size()) return 0;
  return q->elements[idx].width;
}

// §7.12.5 rule (1) -- each element is replaced by the value of the with
// expression. A dynamic-array source (7.5) mapped in place with an int literal
// in the with clause: {1,2,3} + 1 => {2,3,4}, so the last element is 4.
TEST(ArrayMap, ReplacesEachDynamicArrayElement) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int A[] = {1, 2, 3};\n"
      "  int v;\n"
      "  initial begin\n"
      "    A = A.map() with (item + 1'b1);\n"
      "    v = A[2];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 4u);
}

// §7.12.5 rule (3) -- the result keeps the source's range: one element per
// source element, so a three-element source maps to a three-element result.
TEST(ArrayMap, PreservesElementCount) {
  uint64_t sz = RunAndGet(
      "module m;\n"
      "  int A[] = {10, 20, 30};\n"
      "  int R[$];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    R = A.map() with (item * 2);\n"
      "    sz = R.size();\n"
      "  end\n"
      "endmodule\n",
      "sz");
  EXPECT_EQ(sz, 3u);
}

// §7.12.5 rules (1)+(3) -- a map result assigned to a queue target, using the
// iterator index to read a matching element of a second array. With A already
// {2,3,4} and B {2,3,5}: {2+2, 3+3, 4+5} => {4,6,9}, so the last element is 9.
TEST(ArrayMap, ResultAssignedToQueueUsingIndex) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int A[] = {2, 3, 4};\n"
      "  int B[] = {2, 3, 5};\n"
      "  int C[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    C = A.map(a) with (a + B[a.index]);\n"
      "    v = C[2];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 9u);
}

// §7.12.5 rule (1) -- map applies to any unpacked array, including a fixed-size
// one (7.4). Each element is replaced by the with value: {3,6,9} * 2 keeps
// three elements, so the middle result is 12.
TEST(ArrayMap, OverFixedSizeArray) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int fa[3] = '{3, 6, 9};\n"
      "  int R[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    R = fa.map() with (item * 2);\n"
      "    v = R[1];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 12u);
}

// §7.12.5 rule (1) -- a queue source (7.10) is a distinct unpacked-array kind
// with its own element-collection path; map replaces each element the same
// way. {5,15,25} + 1 => {6,16,26}, so the first element is 6.
TEST(ArrayMap, OverQueueSource) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int q[$] = {5, 15, 25};\n"
      "  int R[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    R = q.map() with (item + 1);\n"
      "    v = R[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 6u);
}

// §7.12.5 rule (2) -- each returned element takes the self-determined type of
// the with expression (11.6.1), not the source element type. `item << 4` over a
// byte source is self-determined 8 bits wide, so 8'hFF << 4 truncates to 8'hF0
// (240); a wider result would give 4080. Observing 240 confirms the mapped
// element carries the with expression's own 8-bit width.
TEST(ArrayMap, ElementTakesWithExpressionSelfDeterminedType) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  byte b[] = {8'hFF};\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    q = b.map() with (item << 4);\n"
      "    v = q[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 240u);
}

// §7.12.5 rule (2) -- the self-determined type of the with expression can be
// wider than the source element type, and the returned element keeps that wider
// type rather than being clamped to the source width. `item * 256` over a byte
// source is self-determined 32 bits wide (the 256 literal is an int), so
// 8'hFF * 256 == 65280 survives in full; clamping to 8 bits would give 0.
TEST(ArrayMap, ElementTypeWiderThanSourceElement) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  byte b[] = {8'hFF};\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    q = b.map() with (item * 256);\n"
      "    v = q[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 65280u);
}

// §7.12.5 rule (2) -- a comparison with expression is self-determined 1 bit
// wide, so every mapped element is 1 bit even though the source elements are
// 32-bit ints. Observed directly on the result queue's element width.
TEST(ArrayMap, ElementWidthIsWithExpressionWidth) {
  uint32_t w = RunQueueElemWidth(
      "module m;\n"
      "  int A[] = {1, 2, 3};\n"
      "  bit C[$];\n"
      "  initial C = A.map() with (item > 1);\n"
      "endmodule\n",
      "C", 0);
  EXPECT_EQ(w, 1u);
}

// §7.12.5 rule (2) -- the boolean comparison values themselves are also
// correct. With A {2,3,9} and B {2,3,5}: {2==2, 3==3, 9==5} => {1,1,0}, encoded
// as 1*4 + 1*2 + 0 == 6.
TEST(ArrayMap, BooleanComparisonElements) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int A[] = {2, 3, 9};\n"
      "  int B[] = {2, 3, 5};\n"
      "  bit C[];\n"
      "  int v;\n"
      "  initial begin\n"
      "    C = A.map(a) with (a == B[a.index]);\n"
      "    v = C[0] * 4 + C[1] * 2 + C[2];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 6u);
}

// §7.12.5 rule (3), edge case -- mapping an empty source yields an empty result
// (and is not an error, since the with clause is present).
TEST(ArrayMap, EmptyDynamicSourceYieldsEmptyResult) {
  uint64_t sz = RunAndGet(
      "module m;\n"
      "  int A[];\n"
      "  int R[$];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    R = A.map() with (item + 1);\n"
      "    sz = R.size();\n"
      "  end\n"
      "endmodule\n",
      "sz");
  EXPECT_EQ(sz, 0u);
}

// §7.12.5 rules (1)+(3) for an associative source (7.8) -- map returns an array
// with the same set of index values, each stored value replaced by the with
// expression. The keys carry over unchanged; the value at key 20 (15) becomes
// 15+1 == 16.
TEST(ArrayMap, AssociativeSourcePreservesKeysReplacesValues) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int aa[int];\n"
      "  int bb[int];\n"
      "  int v;\n"
      "  initial begin\n"
      "    aa[10] = 5;\n"
      "    aa[20] = 15;\n"
      "    aa[30] = 25;\n"
      "    bb = aa.map(x) with (x + 1);\n"
      "    v = bb[20];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 16u);
}

// §7.12.5 rule (3) -- the returned associative array's index type matches the
// source. A non-default shortint index carries through: the entry keyed 200
// still exists after the map and its value 8 becomes 8*10 == 80.
TEST(ArrayMap, AssociativeSourcePreservesNonIntIndexType) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int aa[shortint];\n"
      "  int bb[shortint];\n"
      "  int v;\n"
      "  initial begin\n"
      "    aa[100] = 7;\n"
      "    aa[200] = 8;\n"
      "    bb = aa.map(x) with (x * 10);\n"
      "    v = bb[200];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 80u);
}

// §7.12.5 rule (2) for an associative source -- each mapped value also takes
// the self-determined type of the with expression (11.6.1), produced by the
// associative map path (distinct code from the indexed path). With a
// byte-valued source, `x << 4` is self-determined 8 bits wide, so 8'hFF << 4
// truncates to 8'hF0 (240); a wider result would give 4080.
TEST(ArrayMap, AssociativeElementTakesWithExpressionSelfDeterminedType) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  byte aa[int];\n"
      "  int bb[int];\n"
      "  int v;\n"
      "  initial begin\n"
      "    aa[7] = 8'hFF;\n"
      "    bb = aa.map(x) with (x << 4);\n"
      "    v = bb[7];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 240u);
}

// §7.12.5 rules (1)+(3) for a string-keyed associative source -- the index type
// of an associative array (7.8) may be a string, not just an integer type. map
// preserves that string key set and replaces each stored value; the entry keyed
// "hi" (9) becomes 9+1 == 10 and both keys survive.
TEST(ArrayMap, StringKeyedAssociativeSourcePreservesKeys) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int aa[string];\n"
      "  int bb[string];\n"
      "  int v;\n"
      "  initial begin\n"
      "    aa[\"lo\"] = 5;\n"
      "    aa[\"hi\"] = 9;\n"
      "    bb = aa.map(x) with (x + 1);\n"
      "    v = bb[\"hi\"] + bb.size();\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 12u);
}

// §7.12.5 rule (3), edge case for an associative source -- mapping an empty
// associative array yields an empty result with no error.
TEST(ArrayMap, EmptyAssociativeSourceYieldsEmptyResult) {
  uint64_t sz = RunAndGet(
      "module m;\n"
      "  int aa[int];\n"
      "  int bb[int];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    bb = aa.map(x) with (x + 1);\n"
      "    sz = bb.size();\n"
      "  end\n"
      "endmodule\n",
      "sz");
  EXPECT_EQ(sz, 0u);
}

// §7.12.5 rule (1) -- the with clause is required for map(): every element is
// replaced by its value, so a bare map() over an indexed source is an error
// rather than a silent no-op.
TEST(ArrayMap, IndexedSourceRequiresWithClause) {
  EXPECT_TRUE(
      RunProducesError("module m;\n"
                       "  int A[] = {1, 2, 3};\n"
                       "  int R[$];\n"
                       "  initial R = A.map();\n"
                       "endmodule\n"));
}

// §7.12.5 rule (1) -- the with clause is likewise required for map() over an
// associative source; a bare call is an error.
TEST(ArrayMap, AssociativeSourceRequiresWithClause) {
  EXPECT_TRUE(
      RunProducesError("module m;\n"
                       "  int aa[int];\n"
                       "  int bb[int];\n"
                       "  initial begin\n"
                       "    aa[1] = 5;\n"
                       "    bb = aa.map();\n"
                       "  end\n"
                       "endmodule\n"));
}

}  // namespace
