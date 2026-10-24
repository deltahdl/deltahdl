#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

// End-to-end coverage for Annex A §A.2.5 "Declaration ranges". The parser file
// observes each dimension production's AST shape; these tests observe the SAME
// productions manifesting at runtime — the syntactic dimension actually
// produces the aggregate kind it names, seen through the simulated result of an
// operation over that aggregate. Every input is built from real declaration
// syntax and driven through parse -> elaborate -> run; the dependency
// constructs the rules consume (constant_range/constant_expression bounds from
// §A.8.3, the data_type index from §A.2.2.1) are produced by genuine source,
// and each constant bound is exercised as both a literal and a parameter
// because those reach the size through distinct constant-evaluation code paths.

namespace {

// unsized_dimension ::= [ ]  -> a dynamic array. Built with a concatenation
// initializer and reduced with sum(): the reduction can only yield 20 if the []
// declaration produced a four-element dynamic array holding the initializer.
TEST(DeclarationRangeSim, UnsizedDimensionYieldsDynamicArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[] = '{2, 4, 6, 8};\n"
      "  int result;\n"
      "  initial result = a.sum();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

// unpacked_dimension ::= [ constant_expression ]  (size form), literal bound.
// sum() over the four slots is 10 only if the [4] size dimension allocated four
// elements for the initializer.
TEST(DeclarationRangeSim, UnpackedSizeLiteralYieldsFixedArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[4] = '{1, 2, 3, 4};\n"
      "  int result;\n"
      "  initial result = a.sum();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 10u);
}

// unpacked_dimension ::= [ constant_expression ]  where the size is a parameter
// constant expression (§11.2.1), which resolves through the parameter path
// rather than a plain literal. Same observable four-element sum.
TEST(DeclarationRangeSim, UnpackedSizeParameterYieldsFixedArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int P = 4;\n"
      "  int a[P] = '{1, 2, 3, 4};\n"
      "  int result;\n"
      "  initial result = a.sum();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 10u);
}

// unpacked_dimension ::= [ constant_range ]. The [1:3] range yields a
// three-element array; summing the initializer confirms the range sized it.
TEST(DeclarationRangeSim, UnpackedRangeYieldsFixedArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[1:3] = '{10, 20, 30};\n"
      "  int result;\n"
      "  initial result = a.sum();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 60u);
}

// packed_dimension ::= [ constant_range ], literal bound. The [7:0] width makes
// the variable exactly eight bits, so 0xFF + 1 wraps to 0; a wider variable
// would hold 256. The zero result observes the packed width being applied.
TEST(DeclarationRangeSim, PackedRangeLiteralAppliesWidth) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] vec;\n"
      "  int result;\n"
      "  initial begin\n"
      "    vec = 8'hFF;\n"
      "    vec = vec + 8'd1;\n"
      "    result = vec;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// packed_dimension ::= [ constant_range ] whose bounds come from a parameter
// constant expression. The parameter must resolve to width eight for the same
// 0xFF + 1 wrap-to-zero to be observed.
TEST(DeclarationRangeSim, PackedRangeParameterAppliesWidth) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int W = 8;\n"
      "  logic [W-1:0] vec;\n"
      "  int result;\n"
      "  initial begin\n"
      "    vec = 8'hFF;\n"
      "    vec = vec + 8'd1;\n"
      "    result = vec;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// associative_dimension ::= [ data_type ] with an integer index type. Writing
// then reading key 10 exercises the integer-keyed associative array the index
// data type produced.
TEST(DeclarationRangeSim, AssociativeIntegerIndexYieldsAssocArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 55;\n"
      "    result = aa[10];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 55u);
}

// associative_dimension ::= [ data_type ] with a string index type — a
// different admitted data type that produces a string-keyed associative array.
TEST(DeclarationRangeSim, AssociativeStringIndexYieldsAssocArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[\"k\"] = 33;\n"
      "    result = aa[\"k\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 33u);
}

// associative_dimension ::= [ * ]  -> a wildcard-indexed associative array.
TEST(DeclarationRangeSim, AssociativeWildcardYieldsAssocArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[*];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[5] = 77;\n"
      "    result = aa[5];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 77u);
}

// queue_dimension ::= [ $ ]  -> an unbounded queue. Three pushes then size
// confirms the [$] dimension produced a queue that grew dynamically.
TEST(DeclarationRangeSim, QueueUnboundedYieldsQueue) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(1);\n"
      "    q.push_back(2);\n"
      "    q.push_back(3);\n"
      "    result = q.size;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

// queue_dimension ::= [ $ : constant_expression ] with a literal bound. The
// bounded queue still behaves as a queue; pushing three elements (within the
// bound) and reading size observes the bounded-queue form.
TEST(DeclarationRangeSim, QueueBoundedLiteralYieldsQueue) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$:7];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(1);\n"
      "    q.push_back(2);\n"
      "    q.push_back(3);\n"
      "    result = q.size;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

// queue_dimension ::= [ $ : constant_expression ] whose bound is a parameter
// constant expression, resolved through the parameter path.
TEST(DeclarationRangeSim, QueueBoundedParameterYieldsQueue) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int B = 7;\n"
      "  int q[$:B];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(1);\n"
      "    q.push_back(2);\n"
      "    q.push_back(3);\n"
      "    result = q.size;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

// associative_dimension ::= [ data_type ] in a procedural block, with each
// data_type an expression cannot spell: an enumeration, a packed structure, a
// type reference to a 4-bit vector or to string, and a parameterized class.
// Each array keeps its entries: the 4-bit index reads key 17 back as key 1,
// "abcde" and "bcde" are two string keys, and the handle keys its entry. The
// result packs, from the left, e.num(), e[1], s[3], y[1], z.num() and c[h]:
// built as no associative array, a block's array kept no entry at all.
TEST(DeclarationRangeSim, DataTypeIndexFormsInBlockAreAssociative) {
  auto v = RunAndGet(
      "class P #(int N = 1); endclass\n"
      "module t;\n"
      "  bit [3:0] k;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int e [enum {A, B}];\n"
      "    int s [struct packed {bit [3:0] v;}];\n"
      "    int y [type(k)];\n"
      "    int z [type(string)];\n"
      "    int c [P#(8)];\n"
      "    P#(8) h;\n"
      "    h = new;\n"
      "    e[1] = 5;\n"
      "    s[3] = 6;\n"
      "    y[17] = 7;\n"
      "    z[\"abcde\"] = 1;\n"
      "    z[\"bcde\"] = 1;\n"
      "    c[h] = 9;\n"
      "    result = e.num() * 100000 + e[1] * 10000 + s[3] * 1000 +\n"
      "             y[1] * 100 + z.num() * 10 + c[h];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 156729u);
}

// associative_dimension ::= [ data_type ] in a function body: a packed
// structure four bits wide keys key 19 as key 3, so the one entry written
// reads back there. The result packs num() and that entry.
TEST(DeclarationRangeSim, StructureIndexInFunctionBodyIsAssociative) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  function automatic int count();\n"
      "    int a [struct packed {bit [3:0] v;}];\n"
      "    a[19] = 4;\n"
      "    return a.num() * 10 + a[3];\n"
      "  endfunction\n"
      "  initial result = count();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 14u);
}

// associative_dimension ::= [ data_type ] on a class property, written as a
// type reference to the module's 4-bit k: key 18 is key 2. The result packs
// num() and that entry.
TEST(DeclarationRangeSim, TypeRefIndexOfClassPropertyIsAssociative) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [3:0] k;\n"
      "  int result;\n"
      "  class C;\n"
      "    int m [type(k)];\n"
      "  endclass\n"
      "  initial begin\n"
      "    C o;\n"
      "    o = new;\n"
      "    o.m[18] = 3;\n"
      "    result = o.m.num() * 10 + o.m[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 13u);
}

// associative_dimension ::= [ data_type ] on a package's variable: a packed
// structure four bits wide keys key 20 as key 4. The result packs num() and
// that entry.
TEST(DeclarationRangeSim, StructureIndexOfPackageVariableIsAssociative) {
  auto v = RunAndGet(
      "package q;\n"
      "  int a [struct packed {bit [3:0] v;}];\n"
      "endpackage\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    q::a[20] = 6;\n"
      "    result = q::a.num() * 10 + q::a[4];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 16u);
}

// associative_dimension ::= [ data_type ] in a procedural block, the
// data_type a typedef named through its package (§26.3): the 4-bit index
// reads key 17 as key 1, while a constant named the same way, `p::N`, still
// sizes a fixed array of four. The result packs a.num(), a[1] and $size(f).
// Read as no index type, `a` kept no entry.
TEST(DeclarationRangeSim, ScopedTypedefIndexInBlockIsAssociative) {
  auto v = RunAndGet(
      "package p;\n"
      "  typedef bit [3:0] idx_t;\n"
      "  parameter int N = 4;\n"
      "endpackage\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int a [p::idx_t];\n"
      "    int f [p::N];\n"
      "    a[17] = 5;\n"
      "    result = a.num() * 100 + a[1] * 10 + $size(f);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 154u);
}

// The same index in a function body, where key 19 is key 3, and on a class
// property, where key 18 is key 2. The result packs the function's
// a.num() * 10 + a[3], then the property's num() and its entry.
TEST(DeclarationRangeSim, ScopedTypedefIndexInSubroutineAndClassIsAssociative) {
  auto v = RunAndGet(
      "package p;\n"
      "  typedef bit [3:0] idx_t;\n"
      "endpackage\n"
      "module t;\n"
      "  int result;\n"
      "  class C;\n"
      "    int m [p::idx_t];\n"
      "  endclass\n"
      "  function automatic int count();\n"
      "    int a [p::idx_t];\n"
      "    a[19] = 4;\n"
      "    return a.num() * 10 + a[3];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    C o;\n"
      "    o = new;\n"
      "    o.m[18] = 3;\n"
      "    result = count() * 100 + o.m.num() * 10 + o.m[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1413u);
}

// A package's variable indexed by another package's typedef: key 20 is key 4.
// The result packs num() and that entry.
TEST(DeclarationRangeSim, ScopedTypedefIndexOfPackageVariableIsAssociative) {
  auto v = RunAndGet(
      "package p;\n"
      "  typedef bit [3:0] idx_t;\n"
      "endpackage\n"
      "package q;\n"
      "  int a [p::idx_t];\n"
      "endpackage\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    q::a[20] = 6;\n"
      "    result = q::a.num() * 10 + q::a[4];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 16u);
}

// §8.23: a class nested in another is named through the outer one's scope,
// and as an index type keys its array by handle (§7.8.3). Two handles key two
// entries. The result packs num() and the second handle's entry.
TEST(DeclarationRangeSim, NestedClassScopedIndexKeysByHandle) {
  auto v = RunAndGet(
      "class Outer;\n"
      "  class Inner; endclass\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int a [Outer::Inner];\n"
      "    Outer::Inner h1, h2;\n"
      "    h1 = new;\n"
      "    h2 = new;\n"
      "    a[h1] = 8;\n"
      "    a[h2] = 9;\n"
      "    result = a.num() * 10 + a[h2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 29u);
}

}  // namespace
