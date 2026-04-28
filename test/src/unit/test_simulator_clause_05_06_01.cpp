#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

TEST(EscapedIdentifierSim, EscapedIdentAsVariable) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] \\myvar ;\n"
      "  initial \\myvar = 8'd55;\n"
      "endmodule\n",
      "myvar");
  EXPECT_EQ(result, 55u);
}

TEST(EscapedIdentifierSim, EscapedIdentSpecialChars) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] \\data+bus ;\n"
      "  initial \\data+bus = 8'd77;\n"
      "endmodule\n",
      "data+bus");
  EXPECT_EQ(result, 77u);
}

TEST(EscapedIdentifierSim, EscapedKeywordAsVariable) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] \\module ;\n"
      "  initial \\module = 8'd99;\n"
      "endmodule\n",
      "module");
  EXPECT_EQ(result, 99u);
}

TEST(EscapedIdentifierSim, EscapedIdentMultipleVars) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] \\a+b , \\c-d ;\n"
      "  initial begin\n"
      "    \\a+b = 8'd10;\n"
      "    \\c-d = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v1 = f.ctx.FindVariable("a+b");
  auto* v2 = f.ctx.FindVariable("c-d");
  ASSERT_NE(v1, nullptr);
  ASSERT_NE(v2, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 10u);
  EXPECT_EQ(v2->value.ToUint64(), 20u);
}

TEST(EscapedIdentifierSim, EscapedIdentMatchesSimpleIdent) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] cpu3;\n"
      "  initial \\cpu3 = 8'd42;\n"
      "endmodule\n",
      "cpu3");
  EXPECT_EQ(result, 42u);
}

TEST(EscapedIdentifierSim, EscapedIdentDashClock) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] \\-clock ;\n"
      "  initial \\-clock = 8'd11;\n"
      "endmodule\n",
      "-clock");
  EXPECT_EQ(result, 11u);
}

TEST(EscapedIdentifierSim, EscapedIdentInExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] \\x! , result;\n"
      "  initial begin\n"
      "    \\x! = 8'd6;\n"
      "    result = \\x! + 8'd4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(EscapedIdentifierSim, EscapedIdentVariableResolves) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] \\my-var ;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    \\my-var = 99;\n"
      "    y = \\my-var ;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 99u);
}

// §5.6.1: digit-leading body works through simulation as a normal variable.
TEST(EscapedIdentifierSim, EscapedIdentAllDigitsAsVariable) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] \\1234 ;\n"
      "  initial \\1234 = 8'd44;\n"
      "endmodule\n",
      "1234");
  EXPECT_EQ(result, 44u);
}
