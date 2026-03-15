// Non-LRM tests

#include "fixture_elaborator.h"

namespace {

TEST(DesignBuildingBlockElaboration, ProgramWithPortsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p(input clk, input [16:1] addr, inout [7:0] data);\n"
      "  initial begin end\n"
      "endprogram\n",
      f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->ports.size(), 3u);
}

TEST(DesignBuildingBlockElaboration, ProgramWithClassElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  class my_trans;\n"
      "    int data;\n"
      "  endclass\n"
      "endprogram\n",
      f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DesignBuildingBlockElaboration, SampleProgramElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program test (input clk, input [16:1] addr, inout [7:0] data);\n"
      "  initial begin\n"
      "  end\n"
      "endprogram\n",
      f, "test");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramDefinitions, EmptyProgramElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc("program p; endprogram\n", f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
