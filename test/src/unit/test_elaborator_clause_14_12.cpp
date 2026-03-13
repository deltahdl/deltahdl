#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DefaultClockingElab, InlineDefaultClockingElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  default clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(DefaultClockingElab, UnnamedDefaultClockingElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  default clocking @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(DefaultClockingElab, ReferenceFormElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  default clocking cb;\n"
             "endmodule\n"));
}

TEST(DefaultClockingElab, DuplicateDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb1 @(posedge clk1);\n"
      "    input a;\n"
      "  endclocking\n"
      "  default clocking cb2 @(posedge clk2);\n"
      "    input b;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(DefaultClockingElab, DefaultClockingInInterfaceElaborates) {
  EXPECT_TRUE(
      ElabOk("interface my_if (input clk);\n"
             "  logic [7:0] data;\n"
             "  default clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endinterface\n"));
}

}  // namespace
