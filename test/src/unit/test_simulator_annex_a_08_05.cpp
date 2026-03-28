#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LvalueSim, VarLvalueSimpleBlocking) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'h42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x42u);
}

TEST(LvalueSim, NonrangeVarLvalueSimple) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LvalueSim, VarLvalueConcatBlocking) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  initial {a, b} = 8'hC3;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0xCu}, {"b", 0x3u}});
}

TEST(LvalueSim, VarLvalueBitSelectBlocking) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'h00;\n"
      "    x[3] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0x08u}});
}

TEST(LvalueSim, VarLvaluePartSelectBlocking) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'h00;\n"
      "    x[7:4] = 4'hA;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0xA0u}});
}

TEST(LvalueSim, VarLvalueIndexedPartSelectPlusBlocking) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'h00;\n"
      "    x[4+:4] = 4'hB;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0xB0u}});
}

TEST(LvalueSim, VarLvalueMemberAccessBlocking) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = 16'h0000;\n"
      "    p.hi = 8'hAB;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"p", 0xAB00u}});
}

TEST(LvalueSim, VarLvalueStreamingConcatBlocking) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial {>> {a}} = 8'h42;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0x42u}});
}

}  // namespace
