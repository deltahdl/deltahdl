#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "elaborator/concurrent_assert_action.h"
#include "fixture_elaborator.h"
#include "helpers_nested_assertions.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssertActionBlock, RejectsConcurrentAssertionStatements) {
  EXPECT_FALSE(ConcurrentAssertActionBlockAllows(
      ActionBlockStatementForm::kConcurrentAssert));
  EXPECT_FALSE(ConcurrentAssertActionBlockAllows(
      ActionBlockStatementForm::kConcurrentAssume));
  EXPECT_FALSE(ConcurrentAssertActionBlockAllows(
      ActionBlockStatementForm::kConcurrentCover));
}

TEST(AssertActionBlock, AllowsImmediateAssertions) {
  EXPECT_TRUE(ConcurrentAssertActionBlockAllows(
      ActionBlockStatementForm::kImmediateAssertion));
}

TEST(AssertActionBlock, AllowsOrdinaryStatements) {
  EXPECT_TRUE(
      ConcurrentAssertActionBlockAllows(ActionBlockStatementForm::kOther));
}

TEST(AssertActionBlock, AProceduralAssertsNestedAssertIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  always @(posedge clk)\n"
      "    a1: assert property (a) else assert property (b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the action block of a concurrent assert or assume "
                            "statement may not include a concurrent assert, "
                            "assume, or cover statement",
                            4, "16.14.1"));
}

TEST(AssertActionBlock, AProceduralAssumesNestedCoverIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  always @(posedge clk)\n"
      "    a2: assume property (a) cover property (b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the action block of a concurrent assert or assume "
                            "statement may not include a concurrent assert, "
                            "assume, or cover statement",
                            4, "16.14.1"));
}

TEST(AssertActionBlock, AnImmediateAssertionInTheActionBlockIsAllowed) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  always @(posedge clk)\n"
      "    a1: assert property (a) else assert (b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

constexpr const char* kNestingReport =
    "the action block of a concurrent assert or assume statement may not "
    "include a concurrent assert, assume, or cover statement";

std::vector<std::string> AssertOuters() {
  std::vector<std::string> outers;
  for (const char* directive : {"assert", "assume"}) {
    for (const char* position : {"", "else "}) {
      outers.push_back(std::string("x1: ") + directive +
                       " property (@(posedge clk) a) " + position);
    }
  }
  return outers;
}

void ExpectAssertNestingReportedIn(const auto& places, bool procedural) {
  ExpectNestingReportedIn(places,
                          NestingForms(AssertOuters(), kNestedConcurrent),
                          procedural, kNestingReport, "16.14.1");
}

constexpr const char* kModuleOnly[] = {"module"};

TEST(AssertActionBlock,
     EachConcurrentStatementInAProceduralPassOrFailStatementIsReported) {
  ExpectAssertNestingReportedIn(kModuleOnly, true);
}

TEST(AssertActionBlock, ANestedStatementAtAnyDepthInEachProcedureIsReported) {
  ExpectNestingReportedInEachProcedure(NestingDepthForms(AssertOuters()),
                                       kNestingReport, "16.14.1");
}

TEST(AssertActionBlock,
     AProceduralNestingIsReportedInAnInterfaceAProgramAndAChecker) {
  ExpectAssertNestingReportedIn(kNestingDesignUnits, true);
}

TEST(AssertActionBlock, DISABLED_AProceduralNestingIsReportedInAGenerateBlock) {
  ExpectAssertNestingReportedIn(kNestingGenerateBlocks, true);
}

TEST(AssertActionBlock,
     DISABLED_AModuleLevelNestingIsReportedUnderItsOwnRuleInEachPlace) {
  ExpectAssertNestingReportedIn(kNestingPlaces, false);
}

TEST(AssertActionBlock,
     EachImmediateAssertionInAnActionBlockIsAcceptedInEachPlace) {
  ExpectNestingAcceptedEverywhere(
      NestingForms(AssertOuters(), kNestedImmediate));
}

}  // namespace
