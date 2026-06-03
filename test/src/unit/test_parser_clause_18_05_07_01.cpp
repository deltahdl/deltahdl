#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// 18.5.7.1: 'constraint_expression ::= ... | foreach ( array_id [ loop_variables
// ] ) constraint_set'. A foreach iterative constraint with a single loop
// variable and a predicate over the indexed element is a well-formed constraint
// expression and parses without error.
TEST(ForeachIterativeConstraint, SingleLoopVariableAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand byte A[];\n"
      "  constraint c1 { foreach (A[i]) A[i] inside {2, 4, 8, 16}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.7.1: 'loop_variables ::= [ index_variable_identifier ] { , [
// index_variable_identifier ] }'. A list of several loop variables, one per
// array dimension, is accepted.
TEST(ForeachIterativeConstraint, MultipleLoopVariablesAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int A[2][3][4];\n"
      "  constraint c { foreach (A[i, j, k]) A[i][j][k] > 0; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.7.1: an empty loop variable indicates no iteration over that dimension,
// so a position in the loop_variables list may be left blank.
TEST(ForeachIterativeConstraint, EmptyLoopVariableAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int B[2][2][2][2];\n"
      "  constraint c { foreach (B[q, r, , s]) B[q][r][s] > 0; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.7.1: a trailing run of commas may be omitted, so 'foreach (arr[j])' is a
// shorthand for naming only the leading dimension.
TEST(ForeachIterativeConstraint, TrailingCommasOmittedAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int arr[3][4];\n"
      "  constraint c { foreach (arr[j]) arr[j][0] > 0; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.7.1: it shall be an error for any loop variable to have the same
// identifier as the array it iterates over.
TEST(ForeachIterativeConstraint, LoopVariableNameClashRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int A[];\n"
      "  constraint c { foreach (A[A]) A[A] > 0; }\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// 18.5.7.1: the loop-variable naming rule fires on the clashing variable even
// when it is not the first one in a multi-dimensional list.
TEST(ForeachIterativeConstraint, LaterLoopVariableNameClashRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int A[2][3];\n"
      "  constraint c { foreach (A[i, A]) A[i][0] > 0; }\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// 18.5.7.1: a loop variable that merely resembles, but does not equal, the
// array identifier is fine; only an exact match is an error.
TEST(ForeachIterativeConstraint, DistinctLoopVariableAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int A[];\n"
      "  constraint c { foreach (A[a]) A[a] > 0; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.7.1: a foreach iterative constraint's constraint_set may itself contain a
// predicate, such as an implication that guards an element relation against an
// out-of-bounds index. This well-formed sorted-array constraint — whose body
// references the array size and adjacent indexed elements — parses without
// error, confirming the foreach header is recognized and the constraint_set
// after it is scanned normally.
TEST(ForeachIterativeConstraint, PredicatedForeachAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int A[];\n"
      "  constraint c { foreach (A[k]) (k < A.size - 1) -> A[k + 1] > A[k]; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.7.1: the array being iterated may be named by a hierarchical reference,
// and the loop-variable naming rule compares against that array's own
// identifier (the trailing component of the reference). A loop variable that
// matches the trailing array name is still an error.
TEST(ForeachIterativeConstraint, HierarchicalArrayLoopVariableNameClashRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int arr[];\n"
      "  constraint c { foreach (this.arr[arr]) this.arr[arr] > 0; }\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
