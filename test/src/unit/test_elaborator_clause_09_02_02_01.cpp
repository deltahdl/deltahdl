#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §9.2.2.1: always with timing control does not warn.
TEST(ElabClause09_02_02_01, AlwaysWithTimingNoWarning) {
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

// §9.2.2.1: always with event sensitivity does not warn.
TEST(ElabClause09_02_02_01, AlwaysWithSensitivityNoWarning) {
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

// §9.2.2.1: always without any timing control warns about zero-delay loop.
TEST(ElabClause09_02_02_01, AlwaysWithoutTimingWarns) {
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

// §9.2.2.1: always with delay inside begin-end does not warn.
TEST(ElabClause09_02_02_01, AlwaysWithDelayInsideBlockNoWarning) {
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

// §9.2.2.1: always elaborates to RtlirProcessKind::kAlways.
TEST(ElabClause09_02_02_01, AlwaysElaboratesToKAlways) {
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

}  // namespace
