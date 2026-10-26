#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(GeneralPurposeAlwaysElaboration, AlwaysWithTimingNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  always #5 clk = ~clk;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(GeneralPurposeAlwaysElaboration, AlwaysWithSensitivityNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always @(posedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(GeneralPurposeAlwaysElaboration, AlwaysWithStarSensitivityNoWarning) {
  // A general purpose always whose implicit @(*) supplies a sensitivity is
  // not flagged as a potential zero-delay loop: the trigger lets time advance.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, y;\n"
      "  always @* y = a & b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(GeneralPurposeAlwaysElaboration, AlwaysWithoutTimingWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic areg;\n"
      "  always areg = ~areg;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(GeneralPurposeAlwaysElaboration, AlwaysWithDelayInsideBlockNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  always begin\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(GeneralPurposeAlwaysElaboration, AlwaysElaboratesToKAlways) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  always #5 clk = ~clk;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  bool found = false;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kAlways) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(GeneralPurposeAlwaysElaboration, AlwaysWithEventControlInBodyNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always begin\n"
      "    @(posedge clk) q = d;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §9.2.2.1 warns about an always procedure with nothing in it to let simulation
// time advance. A cycle delay is such a control: §14.11 has it hold the process
// for as many clocking block events as it counts, so the process yields and the
// loop is not a zero-delay one. The module carries the default clocking §14.11
// requires of a module using `##`, so nothing else in it is wrong.
TEST(GeneralPurposeAlwaysElaboration, AlwaysWithCycleDelayInBodyNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, d, q, sample;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input sample;\n"
      "  endclocking\n"
      "  always begin\n"
      "    ##3;\n"
      "    q = d;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(GeneralPurposeAlwaysElaboration, AlwaysWithWaitInBodyNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, q;\n"
      "  always begin\n"
      "    wait(en) q = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §9.2.2.1 warns about an always procedure with no control for simulation time
// to advance. Annex P's glossary makes a task enable a blocking statement, the
// task possibly holding one, without the caller looking into its body, so an
// always that enables a task has such a control and draws no warning.
TEST(GeneralPurposeAlwaysElaboration, AlwaysEnablingATaskNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk = 0;\n"
      "  task automatic tick; #5 clk = ~clk; endtask\n"
      "  always begin\n"
      "    tick();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// A function call is no blocking statement, §13.4 keeping every
// time-controlling statement out of a function, so an always whose body only
// calls one still has nothing to let time advance.
TEST(GeneralPurposeAlwaysElaboration, AlwaysCallingOnlyAFunctionWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  function void note; q = ~q; endfunction\n"
      "  always begin\n"
      "    note();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "always block has no timing control", 4,
                              "9.2.2.1"));
}

}  // namespace
