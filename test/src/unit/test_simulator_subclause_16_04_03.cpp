#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(StaticDeferredAssertionSim,
     ModuleLevelDeferredAssertExecutesWithoutProcedure) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a = 1'b0;\n"
      "  logic b = 1'b1;\n"
      "  int fires = 0;\n"
      "  function void count_fire; fires = fires + 1; endfunction\n"
      "  a1: assert #0 (a == b) else count_fire();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("fires");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StaticDeferredAssertionSim,
     ModuleLevelDeferredAssertReevaluatesOnOperandChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a = 1'b0;\n"
      "  logic b = 1'b0;\n"
      "  int fires = 0;\n"
      "  function void count_fire; fires = fires + 1; endfunction\n"
      "  a1: assert #0 (a == b) else count_fire();\n"
      "  initial #1 b = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("fires");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StaticDeferredAssertionSim,
     ModuleLevelDeferredAssertIsFlushedByASecondOperandChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a = 4'd5;\n"
      "  logic [3:0] b = 4'd5;\n"
      "  int fires = 0;\n"
      "  function void count_fire; fires = fires + 1; endfunction\n"
      "  a1: assert #0 (a == b) else count_fire();\n"
      "  initial begin\n"
      "    #1 a = 4'd7;\n"
      "    #0 b = 4'd7;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("fires");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StaticDeferredAssertionSim, ModuleLevelDeferredAssertNamesItsLabel) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a = 1'b0;\n"
      "  logic b = 1'b1;\n"
      "  a1: assert #0 (a == b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityScope(), "m.a1");
  EXPECT_EQ(f.ctx.LastSeverityLine(), 4u);
}

}  // namespace
