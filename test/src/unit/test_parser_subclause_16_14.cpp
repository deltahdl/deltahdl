#include <gtest/gtest.h>

#include <string>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

int UnevaluatedReports(const ParseResult& r) {
  int count = 0;
  for (const auto& diag : r.diags) {
    if (diag.severity == DiagSeverity::kWarning && diag.subclause == "16.14" &&
        diag.message.find("concurrent assertion is not evaluated") !=
            std::string::npos) {
      ++count;
    }
  }
  return count;
}

TEST(ConcurrentAssertionEvaluationReporting,
     AssumePropertyInTheClockedBooleanFormIsEvaluated) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) a);\n"
      "endmodule\n");
  EXPECT_EQ(UnevaluatedReports(r), 0);
}

TEST(ConcurrentAssertionEvaluationReporting,
     AnAssumePropertyBeyondTheEvaluationIsNotEvaluated) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) (b, $display(\"m\")));\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedWarning(
      r.diags, "holds more than the @(event) boolean_expression", 2, "16.14"));
}

TEST(ConcurrentAssertionEvaluationReporting,
     CoverPropertyInTheClockedBooleanFormIsEvaluated) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a);\n"
      "endmodule\n");
  EXPECT_EQ(UnevaluatedReports(r), 0);
}

TEST(ConcurrentAssertionEvaluationReporting,
     ASequentialCoverPropertyIsEvaluated) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_EQ(UnevaluatedReports(r), 0);
}

TEST(ConcurrentAssertionEvaluationReporting, CoverSequenceIsEvaluated) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_EQ(UnevaluatedReports(r), 0);
  auto* item = FindItemByKind(r, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_NE(item->body->assert_sequence, nullptr);
}

TEST(ConcurrentAssertionEvaluationReporting,
     RestrictPropertyGoesUnevaluatedWithoutAReport) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (@(posedge clk) a);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(UnevaluatedReports(r), 0);
}

TEST(ConcurrentAssertionEvaluationReporting, ImplicationsAreEvaluated) {
  auto overlapped = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  EXPECT_EQ(UnevaluatedReports(overlapped), 0);
  auto nonoverlapped = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |=> b);\n"
      "endmodule\n");
  EXPECT_EQ(UnevaluatedReports(nonoverlapped), 0);
}

TEST(ConcurrentAssertionEvaluationReporting,
     CycleDelayIsEvaluatedAsASequentialProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_EQ(UnevaluatedReports(r), 0);
}

TEST(ConcurrentAssertionEvaluationReporting, AssertWithoutAClockIsRead) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a && b);\n"
      "endmodule\n");
  EXPECT_EQ(UnevaluatedReports(r), 0);
  const ModuleItem* assertion = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssertProperty) assertion = item;
  }
  ASSERT_NE(assertion, nullptr);
  EXPECT_TRUE(assertion->sensitivity.empty());
  ASSERT_NE(assertion->body, nullptr);
  EXPECT_TRUE(assertion->body->is_concurrent_clocked);
}

TEST(ConcurrentAssertionEvaluationReporting,
     ABareNameSpecIsLeftToTheElaborator) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a);\n"
      "endmodule\n");
  EXPECT_EQ(UnevaluatedReports(r), 0);
}

TEST(ConcurrentAssertionEvaluationReporting,
     ClockedNonBooleanPropertyIsNotEvaluated) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) (b, $display(\"m\")));\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedWarning(
      r.diags, "holds more than the @(event) boolean_expression", 2, "16.14"));
}

TEST(ConcurrentAssertionEvaluationReporting, ClockedBooleanAssertIsEvaluated) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a);\n"
      "endmodule\n");
  EXPECT_EQ(UnevaluatedReports(r), 0);
}

constexpr const char* kPlacementMessage =
    "a concurrent assertion statement in procedural code shall be in an "
    "always or an initial procedure";

TEST(ConcurrentAssertionPlacement, InAClassMethodIsReported) {
  auto r = Parse(
      "module t;\n"
      "  logic clk; bit x; int f;\n"
      "  class C;\n"
      "    task run();\n"
      "      assert property (@(posedge clk) x) else f++;\n"
      "    endtask\n"
      "  endclass\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, kPlacementMessage, 5, "16.14"));
}

TEST(ConcurrentAssertionPlacement, InAModuleTaskIsReported) {
  auto r = Parse(
      "module t;\n"
      "  logic clk; bit x;\n"
      "  task run();\n"
      "    assume property (@(posedge clk) x);\n"
      "  endtask\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, kPlacementMessage, 4, "16.14"));
}

TEST(ConcurrentAssertionPlacement, InAModuleFunctionIsReported) {
  auto r = Parse(
      "module t;\n"
      "  logic clk; bit x;\n"
      "  function void chk();\n"
      "    cover property (@(posedge clk) x);\n"
      "  endfunction\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, kPlacementMessage, 4, "16.14"));
}

TEST(ConcurrentAssertionPlacement, InAFinalProcedureIsReported) {
  auto r = Parse(
      "module t;\n"
      "  logic clk; bit x;\n"
      "  final begin\n"
      "    cover sequence (@(posedge clk) x);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, kPlacementMessage, 4, "16.14"));
}

TEST(ConcurrentAssertionPlacement, InACoverPassStatementIsLeftToItsOwnRule) {
  auto r = Parse(
      "module t;\n"
      "  logic clk; bit x;\n"
      "  cover property (@(posedge clk) x)\n"
      "    assert property (@(posedge clk) x);\n"
      "endmodule\n");
  for (const auto& diag : r.diags) {
    EXPECT_EQ(diag.message.find(kPlacementMessage), std::string::npos)
        << diag.message;
  }
}

TEST(ConcurrentAssertionPlacement, InAnAlwaysOrAnInitialProcedureIsAccepted) {
  auto r = Parse(
      "module t;\n"
      "  logic clk; bit x;\n"
      "  always @(posedge clk) begin\n"
      "    if (x) assert property (x);\n"
      "  end\n"
      "  always_ff @(posedge clk) cover property (x);\n"
      "  initial begin\n"
      "    assert property (@(posedge clk) x);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
