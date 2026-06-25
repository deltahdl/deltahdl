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
  // A top-level program (no enclosing module) is named as the explicit top so
  // it is actually elaborated; §14.7 permits a clocking block in a program.
  ElabFixture f;
  ElaborateSrc(
      "program p(input clk);\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endprogram\n",
      f, "p");
  EXPECT_FALSE(f.has_errors);
}

TEST(ClockingScopeElab, ClockingInCheckerElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input clk, input data);\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(ClockingScopeElab, ClockingInInterfaceElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "interface intf(input clk, input data);\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endinterface\n",
      f, "intf");
  EXPECT_FALSE(f.has_errors);
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

TEST(ClockingScopeElab, SameBlockNameAcrossInstantiatedScopesElaborates) {
  // §14.7: a clocking block's scope is local to its enclosing module, so the
  // same clocking block name can appear in a module and in a submodule it
  // instantiates without the two colliding during elaboration.
  EXPECT_TRUE(
      ElabOk("module sub;\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"
             "module top;\n"
             "  sub u_sub();\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
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
