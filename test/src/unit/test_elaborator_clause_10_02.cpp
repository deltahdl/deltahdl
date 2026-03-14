#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(AssignmentOverviewElaboration, ProceduralAssignToNet_Blocking_Error) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    w = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AssignmentOverviewElaboration, ProceduralAssignToNet_Nonblocking_Error) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    w <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AssignmentOverviewElaboration, ProceduralAssignToNet_AlwaysBlock_Error) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire clk;\n"
      "  wire w;\n"
      "  always @(posedge clk) begin\n"
      "    w <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AssignmentOverviewElaboration, ProceduralAssignToVariable_Ok) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic v;\n"
      "  initial begin\n"
      "    v = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentOverviewElaboration, ProceduralAssignToRegVariable_Ok) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  reg r;\n"
      "  initial begin\n"
      "    r = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentOverviewElaboration, ProceduralAssignToIntVariable_Ok) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = 42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentOverviewElaboration, ContinuousAssignToNet_Ok) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentOverviewElaboration, ContinuousAssignToVariable_Ok) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic v;\n"
      "  assign v = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentOverviewElaboration, ContAssignConstBitSelect_Ok) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire [7:0] w;\n"
      "  assign w[3] = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentOverviewElaboration, ContAssignNonConstBitSelect_Error) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire [7:0] w;\n"
      "  int idx;\n"
      "  assign w[idx] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AssignmentOverviewElaboration, ContAssignConstPartSelect_Ok) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire [7:0] w;\n"
      "  assign w[3:0] = 4'b1010;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentOverviewElaboration, ContAssignNonConstPartSelect_Error) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire [7:0] w;\n"
      "  int idx;\n"
      "  assign w[idx+:4] = 4'b1010;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AssignmentOverviewElaboration, ContAssignConcatenation_Ok) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire a, b;\n"
      "  assign {a, b} = 2'b10;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentOverviewElaboration, ProceduralNonConstBitSelect_Ok) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  int idx;\n"
      "  initial begin\n"
      "    idx = 3;\n"
      "    v[idx] = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentOverviewElaboration, ProceduralNonConstPartSelect_Ok) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  int idx;\n"
      "  initial begin\n"
      "    idx = 0;\n"
      "    v[idx+:4] = 4'hA;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentOverviewElaboration, ProceduralAssignToTriNet_Error) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  tri n;\n"
      "  initial n = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AssignmentOverviewElaboration, ProceduralAssignToWandNet_Error) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wand n;\n"
      "  initial n = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AssignmentOverviewElaboration, ProceduralAssignToWorNet_Error) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wor n;\n"
      "  initial n = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
