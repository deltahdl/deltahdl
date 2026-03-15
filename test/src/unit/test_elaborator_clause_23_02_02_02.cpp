// §23.2.2.2

#include "fixture_elaborator.h"

namespace {

TEST(AnsiPortDeclarations, ModuleWithInputOutputElaborates) {
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

TEST(AnsiPortDeclarations, CorrectPortCount) {
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

}  // namespace
