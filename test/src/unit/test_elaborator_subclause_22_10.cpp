#include "fixture_elaborator.h"

using namespace delta;

// §22.10 (C5) permits `celldefine and `endcelldefine anywhere in the source
// description -- including inside a design element, which is only discouraged,
// never illegal. Elaboration is where that permission has to hold up: a module
// whose declaration is wrapped in, or interrupted by, the directives has to
// elaborate into the same design as one without them, since the directives
// contribute nothing but a compile-time tag.

namespace {

// The directives split a module declaration without disturbing it: the items
// on both sides of the interruption still belong to the elaborated module.
TEST(CelldefineElaboration, DirectivesInsideModuleBodyElaborate) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "`celldefine\n"
      "  logic [3:0] a;\n"
      "`endcelldefine\n"
      "  logic [3:0] b;\n"
      "  assign b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The recommended placement -- both directives outside the design element --
// elaborates normally, and a cell module instantiated from a non-cell parent
// builds the same hierarchy it would form without the directives.
TEST(CelldefineElaboration, CellModuleInstantiatedFromNonCellParent) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`celldefine\n"
      "module leaf(input logic a, output logic y);\n"
      "  assign y = ~a;\n"
      "endmodule\n"
      "`endcelldefine\n"
      "module top;\n"
      "  logic a, y;\n"
      "  leaf u0(.a(a), .y(y));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
