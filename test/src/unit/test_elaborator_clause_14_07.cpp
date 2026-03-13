#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClockingScopeElab, ClockingInModuleElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingScopeElab, ClockingInProgramElaborates) {
  EXPECT_TRUE(
      ElabOk("program p(input clk);\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endprogram\n"));
}

TEST(ClockingScopeElab, ClockingInCheckerElaborates) {
  EXPECT_TRUE(
      ElabOk("checker chk(input clk, input data);\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endchecker\n"));
}

TEST(ClockingScopeElab, DotAccessToClockvarElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking dom @(posedge clk);\n"
             "    input sig;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    $display(dom.sig);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClockingScopeElab, MultipleBlocksSameModuleElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb1 @(posedge clk);\n"
             "    input a;\n"
             "  endclocking\n"
             "  clocking cb2 @(negedge clk);\n"
             "    output b;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingScopeElab, StaticLifetimeInModule) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    @(cb);\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
