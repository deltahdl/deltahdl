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

TEST(ModuleParametersAndPorts, EmptyPortListElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m(); endmodule\n", f, "m");
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

// In the non-ANSI header style the port characteristic declarations are
// written separately inside the module. §23.2.1 states these are local
// definitions within the module, so the elaborator must resolve them into the
// module's own ports rather than leaving them dangling or external.
TEST(ModuleHeaderDefinition, NonAnsiPortDeclarationsAreLocalToModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(a, b);\n"
      "  input logic a;\n"
      "  output logic b;\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->ports.size(), 2u);
}

TEST(ModuleHeaderDefinition, ModuleWithAttributesElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc("(* synthesis *) module m; endmodule\n", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->top_modules[0]->attrs.empty());
}

}  // namespace
