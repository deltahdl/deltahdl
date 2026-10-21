
#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(DefaultPortValueElaboration, InputPortWithDefaultElaborates) {
  ElabFixture f;
  EXPECT_TRUE(ElabOk("module m(input logic a = 1'b0); endmodule", f));
}

// §23.2.2.2's Syntax 23-4 writes `[ = constant_expression ]` behind a
// variable port's identifier, and its footnote 2 lets only a variable output
// port be initialized and only an input port take a default: on a variable
// output port the expression is the port's initializer, not a §23.2.2.4
// default, and is legal.
TEST(DefaultPortValueElaboration, VariableOutputPortWithInitializerElaborates) {
  ElabFixture f;
  EXPECT_TRUE(ElabOk("module m(output logic q = 1'b0); endmodule", f));
}

// The same footnote's other half: an output port that is a net is no variable
// output port, so it can be neither initialized nor given a default.
TEST(DefaultPortValueElaboration, NetOutputPortWithInitializerIsError) {
  ElabFixture f;
  ElaborateSrc("module m(output wire q = 1'b0); endmodule", f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "initializer on output port 'q', which is a net and no variable", 1,
      "23.2.2.2"));
}

TEST(DefaultPortValueElaboration, InterconnectPortWithDefaultIsError) {
  ElabFixture f;
  ElaborateSrc("module m(input interconnect x = 1'b0); endmodule", f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value on interconnect port 'x'", 1,
                            "23.2.2.4"));
}

TEST(DefaultPortValueElaboration, InoutPortWithDefaultIsError) {
  // §23.2.2.4: a default value is permitted only on an input port. `output` is
  // covered separately; this exercises the `inout` form of the non-input
  // negative. A net data type (wire) is used so the sole diagnostic is the
  // direction rule, not the unrelated "variable on inout port" constraint.
  ElabFixture f;
  ElaborateSrc("module m(inout wire logic [7:0] p = 8'h00); endmodule", f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value on inout port 'p'", 1, "23.2.2.4"));
}

TEST(DefaultPortValueElaboration, RefPortWithDefaultIsError) {
  // §23.2.2.4: the `ref` form of the non-input negative. A ref port is always a
  // singular variable, so the direction rule is the only requirement it trips.
  ElabFixture f;
  ElaborateSrc("module m(ref logic [7:0] p = 8'h00); endmodule", f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value on ref port 'p'", 1, "23.2.2.4"));
}

TEST(DefaultPortValueElaboration, NonSingularPortWithDefaultIsError) {
  ElabFixture f;
  ElaborateSrc("module m(input logic x [3:0] = '{0, 0, 0, 0}); endmodule", f,
               "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value on non-singular port 'x'", 1,
                            "23.2.2.4"));
}

TEST(DefaultPortValueElaboration, OmittedInputUsesDefaultNamedConn) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, input logic [7:0] b = 8'hFF);\n"
      "  assign a = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §23.2.2.4: a default value is a constant expression of the module that
// declares the port, so one reading that module's variable is reported, at
// the port, an integral or a real one alike, while defaults built from its
// parameters, a localparam of its body, a package's parameter, an enumeration
// literal and a constant system function are all constant and are not.
TEST(DefaultPortValueElaboration, NonConstantDefaultIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  parameter int PP = 6;\n"
      "  typedef enum {E0, E1, E2} e_t;\n"
      "endpackage\n"
      "module sub import pk::*; #(parameter int W = 8)\n"
      "  (input var int a = v, input var int b = $clog2(W) + pk::PP,\n"
      "   input var e_t e = E2, input var int g = L, input var real q = v,\n"
      "   output int y);\n"
      "  int v = 3;\n"
      "  localparam int L = 7;\n"
      "  assign y = a;\n"
      "endmodule\n"
      "module top;\n"
      "  int v = 9;\n"
      "  int y;\n"
      "  sub s(.y(y));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value of port 'a' is not a constant "
                            "expression",
                            6, "23.2.2.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value of port 'q' is not a constant "
                            "expression",
                            7, "23.2.2.4"));
  for (const char* port : {"'b'", "'e'", "'g'"}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), port, 6, "23.2.2.4"))
        << port;
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), port, 7, "23.2.2.4"))
        << port;
  }
}

// §23.2.2.4: a default value may be given only in ANSI-style declarations, so
// one written behind a non-ANSI input port's body declaration is reported, at
// the port's place in the header.
TEST(DefaultPortValueElaboration, NonAnsiPortDefaultIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a);\n"
      "  input logic a = 1'b0;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value on port 'a'; defaults are only "
                            "allowed with ANSI-style port declarations",
                            1, "23.2.2.4"));
}

}  // namespace
