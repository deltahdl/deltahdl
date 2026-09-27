#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §31.2: "Like expressions for module path delays, timing check limit values
// are constant expressions that can include specparams." The following tests
// drive real $setup source through parse + elaborate and observe the
// elaborator's constant-operand rule accepting the permitted limit forms and
// rejecting a non-constant one. The dependency machinery (§30.4.2 terminals,
// §30.5 specparam-constant delay expressions) supplies the terminals and the
// specparam declarations the limit is built from.

// A literal is a constant expression, so it is a valid limit.
TEST(TimingCheckLimitConstness, LiteralLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The "can include specparams" clause: a specparam declared in the same
// specify block is an accepted limit operand.
TEST(TimingCheckLimitConstness, SpecparamLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  specify\n"
      "    specparam tSetup = 5;\n"
      "    $setup(d, posedge clk, tSetup);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A constant expression built by combining specparams (exercising the walker's
// recursion into a binary operand) is still a valid limit.
TEST(TimingCheckLimitConstness, SpecparamExpressionLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  specify\n"
      "    specparam tA = 2, tB = 3;\n"
      "    $setup(d, posedge clk, tA + tB);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Negative form: the closest rejected input is a non-constant operand. A
// variable reference is not a constant expression, so it is rejected as a
// timing check limit. Same module shape as the accepting specparam test, with
// only the limit's declaration changed, to isolate this rule.
TEST(TimingCheckLimitConstness, VariableLimitRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  logic [7:0] tSetup;\n"
      "  specify\n"
      "    $setup(d, posedge clk, tSetup);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check limit operand 'tSetup' is not a "
                            "specparam",
                            4, "31.2"));
}

// A non-constant operand buried inside a larger limit expression is still
// rejected: the walker recurses into every operand, so a specparam combined
// with a variable does not launder the variable into a constant.
TEST(TimingCheckLimitConstness, MixedSpecparamAndVariableLimitRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  logic [7:0] w;\n"
      "  specify\n"
      "    specparam tA = 2;\n"
      "    $setup(d, posedge clk, tA + w);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check limit operand 'w' is not a specparam",
                            5, "31.2"));
}

// Negative form, closest constant: a module parameter is a constant expression
// under 11.2.1, yet §31.2 admits only literals and specparams for a limit (like
// module path delays). A parameter operand takes the identifier code path but
// is not in the specparam set, so it is rejected -- distinguishing the literal
// path (accepted above) from the parameter path.
TEST(TimingCheckLimitConstness, ModuleParameterLimitRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  parameter P = 5;\n"
      "  specify\n"
      "    $setup(d, posedge clk, P);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check limit operand 'P' is not a specparam",
                            4, "31.2"));
}

// Negative form, closest constant: a localparam is likewise a constant
// expression under 11.2.1 but not a specparam, so it is also rejected as a
// limit operand -- a distinct declaration path from the module parameter.
TEST(TimingCheckLimitConstness, LocalparamLimitRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  localparam L = 5;\n"
      "  specify\n"
      "    $setup(d, posedge clk, L);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check limit operand 'L' is not a specparam",
                            4, "31.2"));
}

// Syntax 31-2 makes each timing check event a specify_terminal_descriptor,
// whose input_identifier and output_identifier (A.7.3) are a port of the
// module or a member of one of its interface ports. A variable the module
// declares for itself is neither, so a check naming one is refused.
TEST(TimingCheckTerminals, LocalVariableDataEventRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module dut(input clk);\n"
      "  reg d = 0; reg n = 0;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5, n);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check terminal 'd' is not a port of the "
                            "module",
                            4, "31.2"));
}

// The same for a net the module declares, named as the reference event.
TEST(TimingCheckTerminals, LocalNetReferenceEventRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module dut(input d);\n"
      "  wire c;\n"
      "  specify\n"
      "    $hold(posedge c, d, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check terminal 'c' is not a port of the "
                            "module",
                            4, "31.2"));
}

// An input, an inout and an output port are each a terminal: input_identifier
// admits the first two and output_identifier the last two.
TEST(TimingCheckTerminals, PortsOfEveryDirectionAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module dut(input d, inout clk, output q);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5);\n"
      "    $hold(posedge clk, q, 2);\n"
      "    $width(negedge q, 4);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// interface_identifier . port_identifier: a member of an interface port.
TEST(TimingCheckTerminals, InterfacePortMemberAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface bus;\n"
      "  logic d, clk;\n"
      "endinterface\n"
      "module dut(bus b);\n"
      "  specify\n"
      "    $setup(b.d, posedge b.clk, 5);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top;\n"
      "  bus i();\n"
      "  dut u(.b(i));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
