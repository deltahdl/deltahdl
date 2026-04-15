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

TEST(ModuleHeaderDefinition, AutomaticLifetimeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module automatic m(input logic a, output logic y);\n"
      "  assign y = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModuleHeaderDefinition, ModuleWithTimeunitsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModuleHeaderDefinition, WildcardPortsElaborate) {
  EXPECT_TRUE(ElabOk("module m(.*); endmodule\n"));
}

TEST(ModuleHeaderDefinition, ModuleEndLabelElaborates) {
  EXPECT_TRUE(ElabOk("module m; endmodule : m\n"));
}

TEST(ModuleHeaderDefinition, ModuleWithAttributesElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "(* synthesis *) module m; endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->top_modules[0]->attrs.empty());
}

}  // namespace
