#include <gtest/gtest.h>

#include "elaborator/concurrent_assert_action.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §16.14.1: an assert statement's action_block shall not include any concurrent
// assert, assume, or cover statement.
TEST(AssertActionBlock, RejectsConcurrentAssertionStatements) {
  EXPECT_FALSE(ConcurrentAssertActionBlockAllows(
      ActionBlockStatementForm::kConcurrentAssert));
  EXPECT_FALSE(ConcurrentAssertActionBlockAllows(
      ActionBlockStatementForm::kConcurrentAssume));
  EXPECT_FALSE(ConcurrentAssertActionBlockAllows(
      ActionBlockStatementForm::kConcurrentCover));
}

// §16.14.1: the action_block may contain immediate assertion statements.
TEST(AssertActionBlock, AllowsImmediateAssertions) {
  EXPECT_TRUE(ConcurrentAssertActionBlockAllows(
      ActionBlockStatementForm::kImmediateAssertion));
}

// §16.14.1: ordinary statements (e.g. a $display or assignment) are permitted.
TEST(AssertActionBlock, AllowsOrdinaryStatements) {
  EXPECT_TRUE(
      ConcurrentAssertActionBlockAllows(ActionBlockStatementForm::kOther));
}

// §16.14.1: a procedural concurrent assert statement whose fail statement holds
// a concurrent assert is reported.
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

// §16.14.1 with §16.14.2: so is a static assume statement whose pass statement
// holds a concurrent cover.
TEST(AssertActionBlock, AStaticAssumesNestedCoverIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  a2: assume property (@(posedge clk) a)\n"
      "    cover property (@(posedge clk) b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the action block of a concurrent assert or assume "
                            "statement may not include a concurrent assert, "
                            "assume, or cover statement",
                            3, "16.14.1"));
}

// §16.14.1: an immediate assertion in the action block is allowed.
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

}  // namespace
