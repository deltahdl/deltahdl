#include <gtest/gtest.h>

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

}  // namespace
