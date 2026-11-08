#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClockingScopeElab, ClockingInModuleElaborates) {
  EXPECT_TRUE(
      ElabOk("module m; logic clk;\n"
             "  logic data; clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingScopeElab, ClockingInProgramElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "program p(input clk);\n"
      "  logic data; clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endprogram\n",
      f, "p");
  EXPECT_FALSE(f.has_errors);
}

TEST(ClockingScopeElab, ClockingInCheckerElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk, input logic data);\n"
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
      ElabOk("module m; logic clk;\n"
             "  logic sig; clocking dom @(posedge clk);\n"
             "    input sig;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    $display(dom.sig);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClockingScopeElab, MultipleBlocksSameModuleElaborates) {
  EXPECT_TRUE(
      ElabOk("module m; logic clk;\n"
             "  logic a; clocking cb1 @(posedge clk);\n"
             "    input a;\n"
             "  endclocking\n"
             "  logic b; clocking cb2 @(negedge clk);\n"
             "    output b;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingScopeElab, SameBlockNameAcrossInstantiatedScopesElaborates) {
  EXPECT_TRUE(
      ElabOk("module sub; logic clk;\n"
             "  logic data; clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"
             "module top; logic clk;\n"
             "  sub u_sub();\n"
             "  logic data; clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingScopeElab, PerInstanceCopyWhenModuleInstantiatedTwice) {
  EXPECT_TRUE(
      ElabOk("module leaf; logic clk;\n"
             "  logic data; clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"
             "module top;\n"
             "  leaf u0();\n"
             "  leaf u1();\n"
             "endmodule\n"));
}

TEST(ClockingScopeElab, StaticLifetimeInModule) {
  EXPECT_TRUE(
      ElabOk("module m; logic clk;\n"
             "  logic data; clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    @(cb);\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
