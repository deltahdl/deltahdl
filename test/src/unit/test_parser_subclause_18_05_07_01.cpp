#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ForeachIterativeConstraint, SingleLoopVariableAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand byte A[];\n"
      "  constraint c1 { foreach (A[i]) A[i] inside {2, 4, 8, 16}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ForeachIterativeConstraint, MultipleLoopVariablesAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int A[2][3][4];\n"
      "  constraint c { foreach (A[i, j, k]) A[i][j][k] > 0; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ForeachIterativeConstraint, EmptyLoopVariableAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int B[2][2][2][2];\n"
      "  constraint c { foreach (B[q, r, , s]) B[q][r][s] > 0; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ForeachIterativeConstraint, TrailingCommasOmittedAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int arr[3][4];\n"
      "  constraint c { foreach (arr[j]) arr[j][0] > 0; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ForeachIterativeConstraint, LoopVariableNameClashRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int A[];\n"
      "  constraint c { foreach (A[A]) A[A] > 0; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "foreach loop variable 'A' may not have the same "
                            "name as the array it iterates over",
                            3, "18.5.7.1"));
}

TEST(ForeachIterativeConstraint, LaterLoopVariableNameClashRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int A[2][3];\n"
      "  constraint c { foreach (A[i, A]) A[i][0] > 0; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "foreach loop variable 'A' may not have the same "
                            "name as the array it iterates over",
                            3, "18.5.7.1"));
}

TEST(ForeachIterativeConstraint, DistinctLoopVariableAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int A[];\n"
      "  constraint c { foreach (A[a]) A[a] > 0; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ForeachIterativeConstraint, PredicatedForeachAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int A[];\n"
      "  constraint c { foreach (A[k]) (k < A.size - 1) -> A[k + 1] > A[k]; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ForeachIterativeConstraint, FunctionCallArrayIdentifierRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int A[];\n"
      "  constraint c { foreach (f()[i]) A[i] > 0; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a function call may not stand in for the array "
                            "identifier of a foreach iterative constraint",
                            3, "18.5.7.1"));
}

TEST(ForeachIterativeConstraint,
     HierarchicalArrayLoopVariableNameClashRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int arr[];\n"
      "  constraint c { foreach (this.arr[arr]) this.arr[arr] > 0; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "foreach loop variable 'arr' may not have the same "
                            "name as the array it iterates over",
                            3, "18.5.7.1"));
}

TEST(ForeachIterativeConstraint, HierarchicalArrayReferenceAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int arr[3];\n"
      "  constraint c { foreach (this.arr[i]) this.arr[i] > 0; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ForeachIterativeConstraint, BracedConstraintSetAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int A[];\n"
      "  constraint c { foreach (A[i]) { A[i] > 0; A[i] < 100; } }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
