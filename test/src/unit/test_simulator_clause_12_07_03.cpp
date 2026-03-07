#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SimA608, ForeachBasic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    arr[0] = 8'd1;\n"
      "    arr[1] = 8'd2;\n"
      "    arr[2] = 8'd3;\n"
      "    arr[3] = 8'd4;\n"
      "    total = 8'd0;\n"
      "    foreach (arr[i]) total = total + arr[i];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("total");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// §12.7.3: foreach with block body.
TEST(SimA608, ForeachBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [3];\n"
      "  logic [7:0] sum, cnt;\n"
      "  initial begin\n"
      "    arr[0] = 8'd10;\n"
      "    arr[1] = 8'd20;\n"
      "    arr[2] = 8'd30;\n"
      "    sum = 8'd0;\n"
      "    cnt = 8'd0;\n"
      "    foreach (arr[i]) begin\n"
      "      sum = sum + arr[i];\n"
      "      cnt = cnt + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vs = f.ctx.FindVariable("sum");
  auto* vc = f.ctx.FindVariable("cnt");
  ASSERT_NE(vs, nullptr);
  ASSERT_NE(vc, nullptr);
  EXPECT_EQ(vs->value.ToUint64(), 60u);
  EXPECT_EQ(vc->value.ToUint64(), 3u);
}

// §12.7.3: foreach with break — exits loop early.
TEST(SimA608, ForeachBreak) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [5];\n"
      "  logic [7:0] cnt;\n"
      "  initial begin\n"
      "    foreach (arr[i]) arr[i] = 8'd0;\n"
      "    cnt = 8'd0;\n"
      "    foreach (arr[i]) begin\n"
      "      cnt = cnt + 8'd1;\n"
      "      if (cnt == 8'd3) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("cnt");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// §12.7.3: foreach loop variable is read-only and accessible.
TEST(SimA608, ForeachIteratorValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] last_i;\n"
      "  initial begin\n"
      "    foreach (arr[i]) arr[i] = 8'd0;\n"
      "    last_i = 8'd0;\n"
      "    foreach (arr[i]) last_i = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("last_i");
  ASSERT_NE(var, nullptr);
  // Last iteration: i=3.
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

}  // namespace
