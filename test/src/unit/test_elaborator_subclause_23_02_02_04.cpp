
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(DefaultPortValueElaboration, InputPortWithDefaultElaborates) {
  ElabFixture f;
  EXPECT_TRUE(ElabOk("module m(input logic a = 1'b0); endmodule", f));
}

// §23.2.2.2's Syntax 23-4 writes `[ = constant_expression ]` behind a
// variable port's identifier, and its footnote 2 has it "illegal to initialize
// a port that is not a variable output port or to specify a default value for
// a port that is not an input port": on a variable output port the expression
// is the port's initializer, not a §23.2.2.4 default, and is legal.
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

}  // namespace
