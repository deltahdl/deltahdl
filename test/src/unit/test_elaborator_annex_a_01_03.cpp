#include "fixture_elaborator.h"

namespace {

TEST(ModuleParametersAndPorts, ModuleWithInputOutputElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input logic a, output logic y);\n"
      "  assign y = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->top_modules[0]->ports.empty());
}

TEST(ModuleParametersAndPorts, CorrectPortCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module mux2to1 (input wire a, b, sel,\n"
      "                output logic y);\n"
      "  always_comb begin\n"
      "    if (sel) y = a;\n"
      "    else     y = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto* top = design->top_modules[0];
  EXPECT_EQ(top->ports.size(), 4u);
}

TEST(ModuleParametersAndPorts, NonAnsiPortsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->ports.size(), 2u);
}

TEST(ModuleParametersAndPorts, ParameterPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int W = 8)(input logic [W-1:0] d);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModuleParametersAndPorts, EmptyPortListElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(); endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(design->top_modules[0]->ports.empty());
}

}  // namespace
