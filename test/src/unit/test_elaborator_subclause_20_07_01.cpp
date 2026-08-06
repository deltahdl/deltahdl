#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §20.7.1: querying an inner variable-sized dimension is an error.
//
// For `int a[3][][5]`, dimension 1 is the fixed [3], dimension 2 is the dynamic
// [], and dimension 3 is the fixed [5]. Because each element of dimension 1 can
// hold a differently sized dynamic array, $size(a, 2) has no single answer and
// is an error, while the fixed dimensions 1 and 3 are fine. This mirrors the
// example in the LRM.

TEST(ArrayQueryVariableDim, SizeOfDynamicInnerDimensionIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ArrayQueryVariableDim, SizeOfFixedFirstDimensionIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a, 1);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArrayQueryVariableDim, SizeOfFixedInnerDimensionIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a, 3);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// The restriction is on n > 1: the slowest-varying dimension may be queried
// even when it is itself variable-sized (a plain queue is dimension 1).
TEST(ArrayQueryVariableDim, SizeOfQueueFirstDimensionIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int q[$];\n"
      "  int n;\n"
      "  initial n = $size(q, 1);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// A queue nested under a fixed dimension is a variable-sized dimension 2.
TEST(ArrayQueryVariableDim, SizeOfQueueInnerDimensionIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][$];\n"
      "  int n;\n"
      "  initial n = $size(a, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// A wildcard associative array nested under a fixed dimension is likewise a
// variable-sized dimension 2, so querying it is an error.
TEST(ArrayQueryVariableDim, SizeOfWildcardAssocInnerDimensionIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][*];\n"
      "  int n;\n"
      "  initial n = $size(a, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// The LRM example only shows $size, but the restriction applies to every
// per-dimension query function ($left, $right, $low, $high, $increment, $size),
// which all route through the same recognizer. One non-$size function stands in
// for the whole set: $left rejecting an inner dynamic dimension confirms the
// rule is not tied to $size.
TEST(ArrayQueryVariableDim, LeftOfDynamicInnerDimensionIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $left(a, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// The restriction fires wherever the query appears, not only in a procedural
// assignment. A variable declaration initializer is a distinct elaboration walk
// path (the initializer expression rather than a statement body); a variable
// initialized with $size on an inner dynamic dimension is rejected there too.
TEST(ArrayQueryVariableDim, InnerVariableDimInDeclInitializerIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n = $size(a, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// Control for the initializer-position case above: querying a fixed dimension
// from the same declaration-initializer position is legal, confirming the error
// there comes from the variable-sized rule and not from the initializer syntax.
TEST(ArrayQueryVariableDim, FixedDimInDeclInitializerIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n = $size(a, 3);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// The restriction is on a bare array variable. When the first argument resolves
// an outer dimension by indexing (here a[2], a single dynamic array), the query
// targets a well-defined object and is legal even at a dimension that is
// variable-sized for the parent array. This mirrors the $size(a[2], 1) case in
// the LRM example.
TEST(ArrayQueryVariableDim, IndexedElementQueryIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a[2], 1);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.7 states the dimension argument is a constant expression, so the query
// index may be a parameter rather than a literal. Folding it must still surface
// the §20.7.1 error when it names an inner variable-sized dimension. Here the
// parameter value 2 selects the dynamic dimension of a[3][][5].
TEST(ArrayQueryVariableDim, ParameterDimensionIndexIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  parameter int D = 2;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a, D);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// A localparam-valued dimension index that selects a fixed dimension is legal,
// confirming the folded index is compared against the real dimension list and
// not merely rejected for being non-literal.
TEST(ArrayQueryVariableDim, LocalparamDimensionIndexAtFixedDimIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  localparam int D = 3;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a, D);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.7.1: the restriction does not touch $dimensions, which takes no dimension
// argument and so is well-defined even when an inner dimension is variable.
TEST(ArrayQueryVariableDim, DimensionsIsUnaffected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $dimensions(a);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.7.1: the restriction also does not touch $unpacked_dimensions, which
// likewise takes no dimension argument.
TEST(ArrayQueryVariableDim, UnpackedDimensionsIsUnaffected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $unpacked_dimensions(a);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
