#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(ElabSeverityTaskSim, FatalBlocksLowering) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd5;\n"
      "  $fatal(1, \"abort\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_TRUE(design->simulation_blocked);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x"), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "elaboration FATAL in scope 't': abort", 4,
                            "20.10.1"));
}

TEST(ElabSeverityTaskSim, ErrorBlocksLowering) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd5;\n"
      "  $error(\"bad param\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_TRUE(design->simulation_blocked);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x"), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "elaboration ERROR in scope 't': bad param", 4,
                            "20.10.1"));
}

TEST(ElabSeverityTaskSim, WarningDoesNotBlockLowering) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd9;\n"
      "  $warning(\"careful\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->simulation_blocked);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

uint64_t RunAndReadX(const char* src) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (design == nullptr || design->simulation_blocked) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  return var != nullptr ? var->value.ToUint64() : 0;
}

TEST(ElabSeverityTaskSim, InfoDoesNotBlockLowering) {
  EXPECT_EQ(RunAndReadX("module t;\n"
                        "  logic [7:0] x;\n"
                        "  initial x = 8'd9;\n"
                        "  $info(\"fyi\");\n"
                        "endmodule\n"),
            9u);
}

TEST(ElabSeverityTaskSim,
     AWarningOrInfoInAnInterfaceProgramOrCheckerLetsTheDesignRun) {
  EXPECT_EQ(RunAndReadX("interface I;\n"
                        "  $warning(\"i\");\n"
                        "endinterface\n"
                        "program G;\n"
                        "  $info(\"g\");\n"
                        "endprogram\n"
                        "checker c;\n"
                        "  $warning(\"c\");\n"
                        "endchecker\n"
                        "module t;\n"
                        "  logic [7:0] x;\n"
                        "  I i();\n"
                        "  G g();\n"
                        "  c c1();\n"
                        "  initial x = 8'd9;\n"
                        "endmodule\n"),
            9u);
}

}  // namespace
