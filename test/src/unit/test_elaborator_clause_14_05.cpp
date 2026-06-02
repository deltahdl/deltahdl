#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §14.5: a clocking output bound to a hierarchical assignable target (a
// reference to a signal in another scope) is a legal output-port connection
// and elaborates without error.
TEST(ClockingHierExprElab, OutputHierExprElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    output ack = top.dut.ack;\n"
             "  endclocking\n"
             "endmodule\n"));
}

// §14.5: an expression bound to an input clocking signal must be legal for
// connection to a module input port, which accepts any readable expression.
// An operator expression is a valid input-port connection, so it elaborates.
TEST(ClockingHierExprElab, InputAcceptsOperatorExpression) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    input s = top.a + top.b;\n"
             "  endclocking\n"
             "endmodule\n"));
}

// §14.5: an expression bound to an output clocking signal must be legal for
// connection to a module output port, i.e., an assignable target. An operator
// expression is not assignable and is rejected.
TEST(ClockingHierExprElab, OutputRejectsOperatorExpression) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output ack = top.a + top.b;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §14.5: a clocking inout signal must satisfy the output-port connection rule
// as well, so a non-assignable expression bound to an inout signal is rejected.
TEST(ClockingHierExprElab, InoutRejectsOperatorExpression) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    inout d = top.a & top.b;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §14.5: an output bound to a concatenation of assignable targets is a legal
// output-port connection and elaborates without error.
TEST(ClockingHierExprElab, OutputAcceptsConcatenationOfLvalues) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    output bus = { top.hi, top.lo };\n"
             "  endclocking\n"
             "endmodule\n"));
}

// §14.5: a hierarchical expression may be a combination of forms — here a
// concatenation that itself contains a part-select. For an output clocking
// signal every element must remain assignable, so a concatenation combining a
// name with a part-select is a legal output-port connection and elaborates.
TEST(ClockingHierExprElab, OutputAcceptsConcatenationCombiningPartSelect) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    output bus = { top.hi, top.lo[3:1] };\n"
             "  endclocking\n"
             "endmodule\n"));
}

// §14.5: it is acceptable to specify a variable as a clocking inout signal;
// a plain (assignable) name therefore elaborates for the inout direction.
TEST(ClockingHierExprElab, InoutAcceptsVariableName) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout v = top.dut.var_sig;\n"
             "  endclocking\n"
             "endmodule\n"));
}

// §14.5: a simple current-scope name is an assignable target, so it is a legal
// output-port connection for an output clocking signal and elaborates.
TEST(ClockingHierExprElab, OutputAcceptsSimpleName) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    output ack = ack_sig;\n"
             "  endclocking\n"
             "endmodule\n"));
}

// §14.5: a bit/part-select of a signal is an assignable target, so it is a
// legal output-port connection for an output clocking signal and elaborates.
TEST(ClockingHierExprElab, OutputAcceptsPartSelect) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    output nibble = bus[7:4];\n"
             "  endclocking\n"
             "endmodule\n"));
}

// §14.5: a concatenation is a legal output-port connection only if every
// element is itself assignable. An operand that is a non-assignable operator
// expression makes the whole concatenation illegal for an output signal.
TEST(ClockingHierExprElab, OutputRejectsConcatWithNonLvalueElement) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output bus = { top.sig, top.a + top.b };\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}
