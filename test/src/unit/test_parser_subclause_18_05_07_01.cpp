#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_constraint_item_places.h"
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

const char* const kSameName =
    "may not have the same name as the array it iterates over";
const char* const kFunctionArray =
    "a function call may not stand in for the array identifier of a foreach "
    "iterative constraint";
const char* const kItemsDoNotParse =
    "the constraint block's items do not parse from here";
const char* const kArrayAndZ = "int A[4], z;";
const char* const kPackageArray = "package p; int arr[4]; endpackage";
const char* const kHandleClass =
    "class D; int x[4]; function int f(); return 1; endfunction endclass";

struct ForeachReport {
  const char* message;
  int line;
  const char* subclause;
};

void ExpectForeachReport(ItemPlace place, const std::string& decl,
                         const std::string& item, const ForeachReport& report,
                         const std::string& prefix = "") {
  auto r = Parse(ItemIn(place, decl, item, prefix));
  EXPECT_TRUE(
      ReportedError(r.diags, report.message, report.line, report.subclause))
      << ItemPlaceName(place) << ": " << item;
}

void ExpectForeachAccepted(ItemPlace place, const std::string& decl,
                           const std::string& item,
                           const std::string& prefix = "") {
  auto r = Parse(ItemIn(place, decl, item, prefix));
  EXPECT_FALSE(r.has_errors) << ItemPlaceName(place) << ": " << item;
}

TEST(ForeachIterativeConstraint, ALoopVariableNamedAsItsArrayIsRejectedBeyond) {
  for (ItemPlace place : kItemPlacesBeyondTheClass) {
    ExpectForeachReport(place, kArrayAndZ, "foreach (A[A]) z != A[A];",
                        {kSameName, 5, "18.5.7.1"});
  }
}

TEST(ForeachIterativeConstraint, ADistinctLoopVariableIsAcceptedEverywhere) {
  for (ItemPlace place : kEveryItemPlace) {
    ExpectForeachAccepted(place, kArrayAndZ, "foreach (A[i]) z != A[i];");
  }
}

TEST(ForeachIterativeConstraint, ALoopVariableNamedAsAScopedArrayIsRejected) {
  ExpectForeachReport(ItemPlace::kScope, kArrayAndZ,
                      "foreach (p::arr[arr]) z != p::arr[arr];",
                      {kSameName, 6, "18.5.7.1"}, kPackageArray);
  ExpectForeachReport(ItemPlace::kClassBlock, kArrayAndZ,
                      "foreach (C::sa[sa]) z != C::sa[sa];",
                      {kSameName, 5, "18.5.7.1"});
}

TEST(ForeachIterativeConstraint, AScopedArrayNameIsAccepted) {
  ExpectForeachAccepted(ItemPlace::kScope, kArrayAndZ,
                        "foreach (p::arr[i]) z != p::arr[i];", kPackageArray);
  ExpectForeachAccepted(ItemPlace::kClassBlock, kArrayAndZ,
                        "foreach (C::sa[i]) z != C::sa[i];");
}

TEST(ForeachIterativeConstraint, AFunctionCallAsTheArrayIsRejectedBeyond) {
  for (ItemPlace place : kItemPlacesBeyondTheClass) {
    ExpectForeachReport(place, kArrayAndZ, "foreach (f()[i]) z != i;",
                        {kFunctionArray, 5, "18.5.7.1"});
  }
}

TEST(ForeachIterativeConstraint, AMethodCallThroughAHandleIsRejected) {
  ExpectForeachReport(ItemPlace::kClassBlock, "int A[4], z; D h;",
                      "foreach (h.f()[i]) z != i;",
                      {kFunctionArray, 6, "18.5.7.1"}, kHandleClass);
}

TEST(ForeachIterativeConstraint, AnArrayThroughAHandleIsAccepted) {
  ExpectForeachAccepted(ItemPlace::kClassBlock, "int A[4], z; D h;",
                        "foreach (h.x[i]) z != h.x[i];", kHandleClass);
}

TEST(ForeachIterativeConstraint, AnEmptyListAndAnEmptyBracedBodyAreAccepted) {
  for (ItemPlace place : kEveryItemPlace) {
    ExpectForeachAccepted(place, kArrayAndZ, "foreach (A[]) z > 0;");
    ExpectForeachAccepted(place, kArrayAndZ, "foreach (A[i]) {}");
  }
}

TEST(ForeachIterativeConstraint, MalformedForeachConstraintsAreRejected) {
  for (ItemPlace place : kEveryItemPlace) {
    ExpectForeachReport(place, kArrayAndZ, "foreach (A) A[0] == 1;",
                        {kItemsDoNotParse, 5, "A.1.10"});
    ExpectForeachReport(place, kArrayAndZ, "foreach (A[i] A[i] == 1;",
                        {kItemsDoNotParse, 5, "A.1.10"});
    ExpectForeachReport(place, kArrayAndZ, "foreach (A[i]) ;",
                        {kItemsDoNotParse, 5, "A.1.10"});
  }
}

}  // namespace
