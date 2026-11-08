#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(TimeLiteralElaboration, AllSixUnitsElaborate) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial begin\n"
             "    #1fs;\n"
             "    #1ps;\n"
             "    #1ns;\n"
             "    #1us;\n"
             "    #1ms;\n"
             "    #1s;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(TimeLiteralElaboration, TimeLiteralInAssignmentElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  realtime r;\n"
             "  initial r = 5ns;\n"
             "endmodule\n"));
}

TEST(TimeLiteralElaboration, TimeLiteralConstFoldsIntoIntegerParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int P = 3000ps;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_GE(design->top_modules.size(), 1u);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "P");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 3);
}

TEST(TimeLiteralElaboration, TimeLiteralConstFoldsIntoParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int P = 3000ps;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_GE(design->top_modules.size(), 1u);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "P");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 3);
}

TEST(TimeLiteralElaboration, TimeLiteralConstFoldScalesToCurrentUnit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  timeunit 1ps;\n"
      "  timeprecision 1ps;\n"
      "  localparam int P = 3000ps;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_GE(design->top_modules.size(), 1u);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "P");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 3000);
}

TEST(TimeLiteralElaboration, UnitSeparatedFromItsNumberBySpaceIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  initial begin\n"
      "    #2.1 ns;\n"
      "    $display(\"%0t\", $time);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'ns' after the delay 2.1 is a separate token", 4,
                            "5.8"));
}

TEST(TimeLiteralElaboration, UnitJoinedToItsNumberReportsNothing) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  timeunit 1ns;\n"
             "  initial #2.1ns;\n"
             "endmodule\n"));
}

TEST(TimeLiteralElaboration, DelayThenCallOfATaskNamedLikeAUnitIsACall) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  task fs; endtask\n"
             "  initial #2 fs;\n"
             "endmodule\n"));
}

}  // namespace
