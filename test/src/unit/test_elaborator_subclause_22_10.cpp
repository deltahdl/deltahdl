#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

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
