#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ElabCh511, ArrayInitPattern_SimpleArrayOk) {
  SimFixture f;
  ElaborateSrc(
      "module top();\n"
      "  int arr[1:0] = '{10, 20};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SimA60701, PositionalPatternPacksMSBFirst) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    x = '{8'd1, 8'd2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 258u);
}

TEST(SimA60701, SingleElementPositionalPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = '{8'd42};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(SimA60701, FourElementPositionalPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x = '{8'd1, 8'd2, 8'd3, 8'd4};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x01020304u);
}

TEST(SimA60701, PatternInConditionalBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    if (1) x = '{8'd5, 8'd6};\n"
      "    else x = '{8'd0, 8'd0};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1286u);
}

TEST(SimA60701, PatternInCaseItemBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    case(sel)\n"
      "      8'd0: x = '{8'd0, 8'd0};\n"
      "      8'd1: x = '{8'd10, 8'd20};\n"
      "      default: x = '{8'd0, 8'd0};\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 2580u);
}

TEST(SimA60701, PatternInForLoop) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    x = 16'd0;\n"
      "    for (int i = 0; i < 3; i = i + 1) begin\n"
      "      x = '{8'd7, 8'd8};\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1800u);
}

TEST(ElabCh511, ArrayInitPattern_NestedOk) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef struct { int a; int b; } ms_t;\n"
      "  ms_t ms[1:0] = '{'{0, 0}, '{1, 1}};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ElabCh511, ArrayInitPattern_SizeMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  int arr[1:0] = '{10, 20, 30};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabA60701, PatternDefaultKeyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [0:3];\n"
      "  initial begin\n"
      "    arr = '{default: 8'd0};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(ElabCh511, ArrayInitPattern_DuplicateIndex) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  int arr[0:2] = '{0: 1, 1: 2, 0: 3};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SimCh10i, ArrayPositionalPatternInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:1];\n"
      "  initial begin\n"
      "    arr = '{10, 20};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 10u);
  EXPECT_EQ(e1->value.ToUint64(), 20u);
}

TEST(SimCh10i, ArrayDefaultKeyFillsAllElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [0:3];\n"
      "  initial begin\n"
      "    arr = '{default: 8'd42};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  for (int i = 0; i < 4; ++i) {
    auto name = "arr[" + std::to_string(i) + "]";
    auto* elem = f.ctx.FindVariable(name);
    ASSERT_NE(elem, nullptr) << name;
    EXPECT_EQ(elem->value.ToUint64(), 42u) << name;
  }
}

TEST(SimCh10i, ArrayReplicationPatternFills) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:3];\n"
      "  initial begin\n"
      "    arr = '{4{7}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  for (int i = 0; i < 4; ++i) {
    auto name = "arr[" + std::to_string(i) + "]";
    auto* elem = f.ctx.FindVariable(name);
    ASSERT_NE(elem, nullptr) << name;
    EXPECT_EQ(elem->value.ToUint64(), 7u) << name;
  }
}

TEST(SimCh10i, ArrayIndexKeyWithDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:2];\n"
      "  initial begin\n"
      "    arr = '{0: 100, 2: 200, default: 0};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 100u);
  EXPECT_EQ(e1->value.ToUint64(), 0u);
  EXPECT_EQ(e2->value.ToUint64(), 200u);
}

TEST(SimCh10i, ArrayDescendingRangePositional) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [1:0];\n"
      "  initial begin\n"
      "    arr = '{30, 40};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e1->value.ToUint64(), 30u);
  EXPECT_EQ(e0->value.ToUint64(), 40u);
}

TEST(SimCh10i, ArrayVarDeclPatternInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:2] = '{5, 10, 15};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 5u);
  EXPECT_EQ(e1->value.ToUint64(), 10u);
  EXPECT_EQ(e2->value.ToUint64(), 15u);
}

}  // namespace
