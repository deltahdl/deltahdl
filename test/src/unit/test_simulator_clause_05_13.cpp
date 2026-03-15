#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(BuiltinMethodSim, ArraySizeWithParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:3];\n"
      "  logic [31:0] s;\n"
      "  initial s = arr.size();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 4u);
}

TEST(BuiltinMethodSim, ArraySizeNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2];\n"
      "  logic [31:0] s;\n"
      "  initial s = arr.size;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 3u);
}

TEST(BuiltinMethodSim, MethodInExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:4];\n"
      "  logic [31:0] r;\n"
      "  initial r = arr.size() + 32'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 6u);
}

TEST(BuiltinMethodSim, QueuePushBackAndSize) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "  logic [31:0] s;\n"
      "  initial begin\n"
      "    q.push_back(8'hAA);\n"
      "    q.push_back(8'hBB);\n"
      "    s = q.size();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 2u);
}

TEST(BuiltinMethodSim, QueuePushBackElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "  initial begin\n"
      "    q.push_back(8'h42);\n"
      "    q.push_back(8'h43);\n"
      "    q.push_back(8'h44);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 0x42u);
  EXPECT_EQ(q->elements[1].ToUint64(), 0x43u);
  EXPECT_EQ(q->elements[2].ToUint64(), 0x44u);
}

TEST(BuiltinMethodSim, QueuePopFront) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "  logic [31:0] s;\n"
      "  initial begin\n"
      "    q.push_back(8'h10);\n"
      "    q.push_back(8'h20);\n"
      "    q.push_back(8'h30);\n"
      "    q.pop_front();\n"
      "    s = q.size();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 2u);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements[0].ToUint64(), 0x20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 0x30u);
}

TEST(BuiltinMethodSim, ArraySum) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{8'd10, 8'd20, 8'd30};\n"
      "  logic [31:0] total;\n"
      "  initial total = arr.sum();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("total")->value.ToUint64(), 60u);
}

TEST(BuiltinMethodSim, ArrayReverseWithParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{8'hAA, 8'hBB, 8'hCC};\n"
      "  initial arr.reverse();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xCC);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xBB);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xAA);
}

TEST(BuiltinMethodSim, ArrayReverseNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{8'h11, 8'h22, 8'h33};\n"
      "  initial arr.reverse;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x33);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x22);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x11);
}

TEST(BuiltinMethodSim, DynArraySize) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] dyn [] = '{8'hDE, 8'hAD};\n"
      "  logic [31:0] s;\n"
      "  initial s = dyn.size();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 2u);
}

TEST(BuiltinMethodSim, StringLen) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s = \"hello\";\n"
      "  logic [31:0] n;\n"
      "  initial n = s.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("n")->value.ToUint64(), 5u);
}

TEST(BuiltinMethodSim, AssocArrayNum) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int assoc [string];\n"
      "  logic [31:0] n;\n"
      "  initial begin\n"
      "    assoc[\"a\"] = 1;\n"
      "    assoc[\"b\"] = 2;\n"
      "    n = assoc.num();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("n")->value.ToUint64(), 2u);
}

TEST(BuiltinMethodSim, QueueSizeNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "  logic [31:0] s;\n"
      "  initial begin\n"
      "    q.push_back(8'h01);\n"
      "    q.push_back(8'h02);\n"
      "    q.push_back(8'h03);\n"
      "    s = q.size;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 3u);
}

TEST(BuiltinMethodSim, EnumNum) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_e;\n"
      "  color_e c;\n"
      "  logic [31:0] n;\n"
      "  initial n = c.num();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("n")->value.ToUint64(), 3u);
}

TEST(BuiltinMethodSim, MethodResultInConditional) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "  logic [31:0] r;\n"
      "  initial begin\n"
      "    q.push_back(8'hFF);\n"
      "    if (q.size() > 0)\n"
      "      r = 32'd1;\n"
      "    else\n"
      "      r = 32'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 1u);
}

}  // namespace
