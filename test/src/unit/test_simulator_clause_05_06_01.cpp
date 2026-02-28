
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "preprocessor/preprocessor.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

// §5.6.1 Escaped identifiers

TEST(SimCh50601, EscapedIdentAsVariable) {
  // §5.6.1: Escaped identifiers can name variables.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] \\myvar ;\n"
      "  initial \\myvar = 8'd55;\n"
      "endmodule\n",
      "\\myvar");
  EXPECT_EQ(result, 55u);
}

TEST(SimCh50601, EscapedIdentSpecialChars) {
  // §5.6.1: Escaped identifiers may include printable ASCII 33-126.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] \\data+bus ;\n"
      "  initial \\data+bus = 8'd77;\n"
      "endmodule\n",
      "\\data+bus");
  EXPECT_EQ(result, 77u);
}

TEST(SimCh50601, EscapedKeywordAsVariable) {
  // §5.6.1: An escaped keyword is treated as a user-defined identifier.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] \\module ;\n"
      "  initial \\module = 8'd99;\n"
      "endmodule\n",
      "\\module");
  EXPECT_EQ(result, 99u);
}

TEST(SimCh50601, EscapedIdentMultipleVars) {
  // §5.6.1: Multiple escaped identifiers in the same module.
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
  auto* v1 = f.ctx.FindVariable("\\a+b");
  auto* v2 = f.ctx.FindVariable("\\c-d");
  ASSERT_NE(v1, nullptr);
  ASSERT_NE(v2, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 10u);
  EXPECT_EQ(v2->value.ToUint64(), 20u);
}

TEST(SimCh50601, EscapedIdentInExpression) {
  // §5.6.1: Escaped identifiers used in expressions.
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
