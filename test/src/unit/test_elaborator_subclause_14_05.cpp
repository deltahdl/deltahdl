#include <gtest/gtest.h>

#include <format>
#include <initializer_list>
#include <tuple>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClockingHierExprElab, OutputHierExprElaborates) {
  EXPECT_TRUE(
      ElabOk("module m; logic clk;\n"
             "  clocking cb @(posedge clk);\n"
             "    output ack = top.dut.ack;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingHierExprElab, InputAcceptsOperatorExpression) {
  EXPECT_TRUE(
      ElabOk("module m; logic clk;\n"
             "  clocking cb @(posedge clk);\n"
             "    input s = top.a + top.b;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingHierExprElab, OutputRejectsOperatorExpression) {
  ElabFixture f;
  ElaborateSrc(
      "module m; logic clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    output ack = top.a + top.b;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "clocking output signal 'ack' is bound to an "
                            "expression that is not a legal output-port "
                            "connection",
                            3, "14.5"));
}

TEST(ClockingHierExprElab, InoutRejectsOperatorExpression) {
  ElabFixture f;
  ElaborateSrc(
      "module m; logic clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    inout d = top.a & top.b;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "clocking inout signal 'd' is bound to an "
                            "expression that is not a legal output-port "
                            "connection",
                            3, "14.5"));
}

TEST(ClockingHierExprElab, OutputAcceptsConcatenationOfLvalues) {
  EXPECT_TRUE(
      ElabOk("module m; logic clk;\n"
             "  clocking cb @(posedge clk);\n"
             "    output bus = { top.hi, top.lo };\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingHierExprElab, OutputAcceptsConcatenationCombiningPartSelect) {
  EXPECT_TRUE(
      ElabOk("module m; logic clk;\n"
             "  clocking cb @(posedge clk);\n"
             "    output bus = { top.hi, top.lo[3:1] };\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingHierExprElab, InoutAcceptsVariableName) {
  EXPECT_TRUE(
      ElabOk("module m; logic clk;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout v = top.dut.var_sig;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingHierExprElab, OutputAcceptsSimpleName) {
  EXPECT_TRUE(
      ElabOk("module m; logic clk;\n"
             "  clocking cb @(posedge clk);\n"
             "    output ack = ack_sig;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingHierExprElab, OutputAcceptsPartSelect) {
  EXPECT_TRUE(
      ElabOk("module m; logic clk;\n"
             "  clocking cb @(posedge clk);\n"
             "    output nibble = bus[7:4];\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingHierExprElab, OutputRejectsConcatWithNonLvalueElement) {
  ElabFixture f;
  ElaborateSrc(
      "module m; logic clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    output bus = { top.sig, top.a + top.b };\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "clocking output signal 'bus' is bound to an "
                            "expression that is not a legal output-port "
                            "connection",
                            3, "14.5"));
}

TEST(ClockingHierExprElab,
     EachExpressionIsJudgedAsAPortConnectionOfItsDirection) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, s;\n"
      "  logic [3:0] a, b, c;\n"
      "  function automatic logic [3:0] fn(); return 4'd1; endfunction\n"
      "  clocking cb @(posedge clk);\n"
      "    output o1 = 4'd3;\n"
      "    output o2 = fn();\n"
      "    output o3 = {2{a[1:0]}};\n"
      "    output o4 = s ? a : b;\n"
      "    inout  o5 = 4'd2;\n"
      "    output o6 = {a[1:0], b[3:2]};\n"
      "    inout  o7 = {c, s};\n"
      "    input  i1 = 4'd3;\n"
      "    input  i2 = fn();\n"
      "    input  i3 = {2{a[1:0]}};\n"
      "    input  i4 = s ? a : b;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  for (auto [dir, name, line] :
       {std::tuple{"output", "o1", 6u}, std::tuple{"output", "o2", 7u},
        std::tuple{"output", "o3", 8u}, std::tuple{"output", "o4", 9u},
        std::tuple{"inout", "o5", 10u}}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("clocking {} signal '{}' is bound to an expression that "
                    "is not a legal output-port connection",
                    dir, name),
        line, "14.5"))
        << name;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 5u);
}

}  // namespace
