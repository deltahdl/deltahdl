#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(HardwareModelExecutionElaboration, EmptyModuleElaboratesWithNoPorts) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module empty;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_TRUE(mod->ports.empty());
  EXPECT_TRUE(mod->processes.empty());
  EXPECT_TRUE(mod->assigns.empty());
  EXPECT_TRUE(mod->children.empty());
}

TEST(HardwareModelExecutionElaboration, ModuleWithPortsElaboratesPorts) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 2u);
}

TEST(HardwareModelExecutionElaboration, DesignWithVariablesAndProcesses) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic clk;\n"
      "  logic [7:0] count;\n"
      "  initial count = 0;\n"
      "  always_ff @(posedge clk) count <= count + 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->variables.size(), 2u);
  EXPECT_EQ(mod->processes.size(), 2u);
}

}  // namespace
