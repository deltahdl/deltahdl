#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ProceduralAssignDeassignElaboration, AssignSingularVariableLhs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration, AssignConcatenationLhs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    assign {a, b} = 2'b10;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration, AssignBitSelectLhsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  reg [7:0] data;\n"
      "  initial begin\n"
      "    assign data[3] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration, AssignPartSelectLhsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  reg [7:0] data;\n"
      "  initial begin\n"
      "    assign data[3:0] = 4'hA;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration, DeassignSingularVariableLhs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 1;\n"
      "    deassign q;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration, DeassignConcatenationLhs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    assign {a, b} = 2'b10;\n"
      "    deassign {a, b};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration, AssignVectorLhs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg [15:0] vec;\n"
      "  initial begin\n"
      "    assign vec = 16'hDEAD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration, AssignInAlwaysBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg q;\n"
      "  reg clear, preset;\n"
      "  always @(clear or preset)\n"
      "    if (!clear)\n"
      "      assign q = 0;\n"
      "    else if (!preset)\n"
      "      assign q = 1;\n"
      "    else\n"
      "      deassign q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration, AssignIndexedPartSelectLhsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  reg [7:0] data;\n"
      "  initial begin\n"
      "    assign data[3+:4] = 4'hA;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration, ReAssignSameVariableElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 0;\n"
      "    assign q = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
