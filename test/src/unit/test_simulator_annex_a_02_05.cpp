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

}  // namespace
