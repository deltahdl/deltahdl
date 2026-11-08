#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

namespace {

TEST(ModuleContents, MixedItemsElaborate) {
  EXPECT_TRUE(
      ElabOk("module m (input logic clk, output logic [7:0] q);\n"
             "  wire [7:0] net;\n"
             "  logic [7:0] dat;\n"
             "  localparam int HALF = 4;\n"
             "  assign net = dat;\n"
             "  always_comb dat = ~q;\n"
             "  always_ff @(posedge clk) q <= net;\n"
             "endmodule\n"));
}

TEST(ModuleItemsElaboration, EmptyModuleElaborates) {
  ElabFixture f;
  auto* design = Elaborate("module m; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(design->top_modules[0]->processes.empty());
  EXPECT_TRUE(design->top_modules[0]->assigns.empty());
  EXPECT_TRUE(design->top_modules[0]->children.empty());
}

TEST(ModuleItemsElaboration, ContinuousAssignElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a;\n"
      "  assign a = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->top_modules[0]->assigns.empty());
}

TEST(ModuleItemsElaboration, InitialBlockElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  initial begin end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules[0]->processes.empty());
  EXPECT_EQ(design->top_modules[0]->processes[0].kind,
            RtlirProcessKind::kInitial);
}

TEST(ModuleItemsElaboration, FinalBlockElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  final begin end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules[0]->processes.empty());
  EXPECT_EQ(design->top_modules[0]->processes[0].kind,
            RtlirProcessKind::kFinal);
}

TEST(ModuleItemsElaboration, AlwaysCombProcessKind) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  always_comb begin end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules[0]->processes.empty());
  EXPECT_EQ(design->top_modules[0]->processes[0].kind,
            RtlirProcessKind::kAlwaysComb);
}

TEST(ModuleItemsElaboration, ModuleInstantiationElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module child; endmodule\n"
      "module m;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->top_modules[0]->children.empty());
  EXPECT_EQ(design->top_modules[0]->children[0].module_name, "child");
  EXPECT_EQ(design->top_modules[0]->children[0].inst_name, "u1");
}

TEST(ModuleItemsElaboration, ConditionalGenerateElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  if (1) begin : yes\n"
      "    wire a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModuleItemsElaboration, LoopGenerateElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : blk\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModuleItemsElaboration, GenerateRegionElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  generate\n"
      "    wire w;\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModuleItemsElaboration, NetAliasElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w1, w2;\n"
      "  alias w1 = w2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->top_modules[0]->aliases.empty());
}

TEST(ModuleItemsElaboration, GateInstantiationElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModuleItemsElaboration, SpecparamElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam delay = 10;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModuleItemsElaboration, SpecifyBlockElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input a, output y);\n"
      "  assign y = a;\n"
      "  specify\n"
      "    (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModuleItemsElaboration, ClockingBlockElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic clk;\n"
      "  clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModuleItemsElaboration, ElabSystemTaskElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  $info(\"build info\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
