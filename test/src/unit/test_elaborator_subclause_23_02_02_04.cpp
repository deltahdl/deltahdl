#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(DefaultPortValueElaboration, InputPortWithDefaultElaborates) {
  ElabFixture f;
  EXPECT_TRUE(ElabOk("module m(input logic a = 1'b0); endmodule", f));
}

TEST(DefaultPortValueElaboration, VariableOutputPortWithInitializerElaborates) {
  ElabFixture f;
  EXPECT_TRUE(ElabOk("module m(output logic q = 1'b0); endmodule", f));
}

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
  ElabFixture f;
  ElaborateSrc("module m(inout wire logic [7:0] p = 8'h00); endmodule", f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value on inout port 'p'", 1, "23.2.2.4"));
}

TEST(DefaultPortValueElaboration, RefPortWithDefaultIsError) {
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
