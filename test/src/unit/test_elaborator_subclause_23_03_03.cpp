
#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PortConnectionRulesElaboration, CompatibleIntegralTypesAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input logic [7:0] a, output logic [7:0] b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module top;\n"
             "  bit [7:0] x;\n"
             "  logic [7:0] y;\n"
             "  child u(.a(x), .b(y));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesElaboration, DifferentWidthIntegralsAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input logic [7:0] a, output logic [7:0] b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module top;\n"
             "  logic [3:0] x;\n"
             "  logic [7:0] y;\n"
             "  child u(.a(x), .b(y));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesElaboration, RealToIntegralPortAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input integer a, output integer b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module top;\n"
             "  real x;\n"
             "  integer y;\n"
             "  child u(.a(x), .b(y));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesElaboration, IncompatibleTypesOnPortConnectionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input logic [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  string s;\n"
      "  child u(.a(s));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "not assignment compatible with port 'a'", 5,
                            "23.3.3"));
}

TEST(PortConnectionRulesElaboration, NettypeSignalOnInputPortAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input logic [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  nettype logic [7:0] mytype;\n"
             "  mytype x;\n"
             "  child u(.a(x));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesElaboration, NettypeSignalOnOutputPortAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input logic [7:0] a, output logic [7:0] b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module top;\n"
             "  nettype logic [7:0] mytype;\n"
             "  logic [7:0] x;\n"
             "  mytype y;\n"
             "  child u(.a(x), .b(y));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesElaboration, NettypeSignalOnInoutPortErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(inout wire [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  nettype logic [7:0] mytype;\n"
      "  mytype x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "user-defined nettype signal 'x' cannot connect to "
                            "inout port 'a'",
                            6, "23.3.3"));
}

// §23.3.3: a port with a user-defined nettype on one side only is an input or
// an output, so an inout port declared with the nettype and joined to an
// ordinary wire is reported, as one joined to a net of the nettype is not.
TEST(PortConnectionRulesElaboration, InoutPortOfANettypeOnAPlainNetErrors) {
  ElabFixture f;
  ElaborateSrc(
      "typedef logic [7:0] T;\n"
      "nettype T mynet;\n"
      "module child(inout mynet q);\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] w;\n"
      "  mynet n;\n"
      "  child u1(.q(w));\n"
      "  child u2(.q(n));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "inout port 'q' of user-defined nettype 'mynet'", 8,
                            "23.3.3"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "inout port 'q'", 9, "23.3.3"));
}

// §23.3.3: where only one side of a port connection is of a user-defined
// nettype, the two sides' data types match. A nettype port joined to a signed
// vector or to an int, and a 2-state port joined to a nettype net, are each
// reported, whichever side carries the nettype; a logic vector of the
// nettype's width joined either way is not.
TEST(PortConnectionRulesElaboration,
     OneSidedNettypeOfNonMatchingDataTypeErrors) {
  ElabFixture f;
  ElaborateSrc(
      "typedef logic [7:0] T;\n"
      "nettype T mynet;\n"
      "module child(input mynet p, input mynet s, input var bit [7:0] r,\n"
      "             input logic [7:0] k);\n"
      "endmodule\n"
      "module top;\n"
      "  logic signed [7:0] a;\n"
      "  logic [7:0] okv;\n"
      "  mynet n, m;\n"
      "  int i;\n"
      "  child u1(.p(a), .s(okv), .r(n), .k(m));\n"
      "  child u2(.p(i), .s(okv), .r(n), .k(m));\n"
      "endmodule\n",
      f);
  const char* message = "to a connection whose data type does not match it";
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "port 'p' joins", 11, "23.3.3"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "port 'r' joins", 11, "23.3.3"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "port 'p' joins", 12, "23.3.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 12, "23.3.3"));
  for (const char* port : {"port 's'", "port 'k'"}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), port, 11, "23.3.3"))
        << port;
  }
}

TEST(PortConnectionRulesElaboration, InputPortConnectionIsSourceToSink) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] src;\n"
      "  child u(.a(src));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->children.size(), 1u);
}

// A binding records whether the instantiation wrote its connection: an
// empty `.n()`, a port left out of `.*` and a trailing input each stand
// unconnected though the elaborator supplies a value in their place, and a
// written connection does not (§23.3.3, for §37.14 detail 10's vpiHighConn).
TEST(PortConnectionRulesElaboration, AnUnwrittenConnectionIsMarkedUnconnected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module sub(input logic a, input logic n, input logic t); endmodule\n"
      "module top; logic w; sub u(.a(w), .n()); endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const auto& top = *design->top_modules[0];
  ASSERT_EQ(top.children.size(), 1U);
  bool saw_a = false;
  for (const auto& binding : top.children[0].port_bindings) {
    if (binding.port_name == "a") {
      saw_a = true;
      EXPECT_FALSE(binding.unconnected);
    } else {
      EXPECT_TRUE(binding.unconnected) << binding.port_name;
    }
  }
  EXPECT_TRUE(saw_a);
}

// A port of a user-defined nettype is connected to a net of a matching nettype,
// and a nettype written through its package is that package's on either side:
// c's port of P::nt meets m's net of P::nt2, a different nettype, which is
// reported, and m's net of P::nt, which is not (#7600).
TEST(PortConnectionRulesElaboration, PackageScopedNettypesMatchedAcrossAPort) {
  ElabFixture f;
  ElaborateSrc(
      "package P;\n"
      "  nettype logic [3:0] nt;\n"
      "  nettype logic [3:0] nt2;\n"
      "endpackage\n"
      "module c(input P::nt p);\n"
      "endmodule\n"
      "module m;\n"
      "  P::nt a;\n"
      "  P::nt2 b;\n"
      "  c u1(.p(a));\n"
      "  c u2(.p(b));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "port 'p' connects user-defined nettype 'P::nt' on "
                    "the instance side to non-matching nettype 'P::nt2'",
                    11, "23.3.3"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "port 'p' connects", 10, "23.3.3"));
}

}  // namespace
