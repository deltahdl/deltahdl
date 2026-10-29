
#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PortConnectionRulesForNetsElaboration,
     InputNetPortConnectsToCompatibleExpression) {
  EXPECT_TRUE(
      ElabOk("module child(input wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] x;\n"
             "  child u(.a(x + 8'd1));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration, InputNetPortConnectsToNet) {
  EXPECT_TRUE(
      ElabOk("module child(input wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  wire [7:0] w;\n"
             "  child u(.a(w));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration, InputNetPortConnectsToVariable) {
  EXPECT_TRUE(
      ElabOk("module child(input wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] v;\n"
             "  child u(.a(v));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration, InputNetPortConnectsToLiteral) {
  EXPECT_TRUE(
      ElabOk("module child(input wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  child u(.a(8'hFF));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration, InputTriPortConnectsToExpression) {
  EXPECT_TRUE(
      ElabOk("module child(input tri [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] x;\n"
             "  child u(.a(x));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration, UnconnectedInputNetPortNoError) {
  EXPECT_TRUE(
      ElabOk("module child(input wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  child u();\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration,
     UnconnectedInputNetPortNamedNoError) {
  EXPECT_TRUE(
      ElabOk("module child(input wire [7:0] a, input wire b);\n"
             "endmodule\n"
             "module top;\n"
             "  wire w;\n"
             "  child u(.b(w));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration, OutputNetPortConnectsToNet) {
  EXPECT_TRUE(
      ElabOk("module child(output wire [7:0] y);\n"
             "  assign y = 8'hAB;\n"
             "endmodule\n"
             "module top;\n"
             "  wire [7:0] w;\n"
             "  child u(.y(w));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration, OutputNetPortConnectsToVariable) {
  EXPECT_TRUE(
      ElabOk("module child(output wire [7:0] y);\n"
             "  assign y = 8'hAB;\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] v;\n"
             "  child u(.y(v));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration,
     OutputNetPortConnectsToConcatenation) {
  EXPECT_TRUE(
      ElabOk("module child(output wire [7:0] y);\n"
             "  assign y = 8'hAB;\n"
             "endmodule\n"
             "module top;\n"
             "  logic [3:0] hi, lo;\n"
             "  child u(.y({hi, lo}));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration, OutputTriPortConnectsToNet) {
  EXPECT_TRUE(
      ElabOk("module child(output tri y);\n"
             "  assign y = 1'b1;\n"
             "endmodule\n"
             "module top;\n"
             "  wire w;\n"
             "  child u(.y(w));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration, InoutNetPortConnectsToNet) {
  EXPECT_TRUE(
      ElabOk("module child(inout wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  wire [7:0] w;\n"
             "  child u(.a(w));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration,
     InoutNetPortConnectsToConcatenationOfNets) {
  EXPECT_TRUE(
      ElabOk("module child(inout wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  wire [3:0] hi, lo;\n"
             "  child u(.a({hi, lo}));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration, InoutTriPortConnectsToNet) {
  EXPECT_TRUE(
      ElabOk("module child(inout tri data);\n"
             "endmodule\n"
             "module top;\n"
             "  wire w;\n"
             "  child u(.data(w));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration,
     InoutNetPortLeftUnconnectedNoError) {
  EXPECT_TRUE(
      ElabOk("module child(inout wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  child u();\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration, InoutNetPortOmittedByNameNoError) {
  EXPECT_TRUE(
      ElabOk("module child(inout wire [7:0] a, input wire b);\n"
             "endmodule\n"
             "module top;\n"
             "  wire w;\n"
             "  child u(.b(w));\n"
             "endmodule\n"));
}

// §23.3.3.3 governs a port declaration with a net type, wire for one, and its
// inout rule lets an inout connect to a net, or a concatenation of nets, of a
// compatible data type, or stay unconnected, but never connect to a variable.
// The port here is declared `inout wire`, so it is this rule rather than
// §23.3.3.2's, which opens on a port declared with a variable data type.
TEST(PortConnectionRulesForNetsElaboration,
     VariableConnectedToInoutNetPortErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(inout wire [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'x' cannot be connected to inout port 'a'", 5, "23.3.3.3"));
}

// §23.3.3.3's inout rule is about what the connection is, not about how the
// port was bound, so a positional connection of the same variable is rejected
// under the same subclause.
TEST(PortConnectionRulesForNetsElaboration,
     VariableConnectedToInoutNetPortPositionalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(inout wire [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  child u(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'x' cannot be connected to inout port 'a'", 5, "23.3.3.3"));
}

// An input net port admits any compatible expression, including a constant
// parameter reference. A parameter resolves through a different elaboration
// path than a folded literal, so it is exercised as its own operand form.
TEST(PortConnectionRulesForNetsElaboration, InputNetPortConnectsToParameter) {
  EXPECT_TRUE(
      ElabOk("module child(input wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  parameter logic [7:0] P = 8'h3C;\n"
             "  child u(.a(P));\n"
             "endmodule\n"));
}

// A localparam constant is another admitted operand for an input net port
// connection, resolved distinctly from a parameter or a literal.
TEST(PortConnectionRulesForNetsElaboration, InputNetPortConnectsToLocalparam) {
  EXPECT_TRUE(
      ElabOk("module child(input wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  localparam logic [7:0] L = 8'h5A;\n"
             "  child u(.a(L));\n"
             "endmodule\n"));
}

// The input-net connection rule holds regardless of whether the port is bound
// by name or by position; a positional compatible connection is equally legal.
TEST(PortConnectionRulesForNetsElaboration, InputNetPortConnectsPositionally) {
  EXPECT_TRUE(
      ElabOk("module child(input wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] x;\n"
             "  child u(x);\n"
             "endmodule\n"));
}

// A design whose line 7 connects `connection` to the two-bit inout port `a` of
// `child`, the parent having the nets `w` and `n` and the variables `v` and
// `b`, the last one bit wide.
std::string InoutConnectedTo(const std::string& connection) {
  return "module child(inout wire [1:0] a);\n"
         "endmodule\n"
         "module top;\n"
         "  wire [3:0] w, n;\n"
         "  logic [3:0] v;\n"
         "  logic b;\n"
         "  child u(" +
         connection +
         ");\n"
         "endmodule\n";
}

// §23.3.3.3 (printed page 747) connects an inout port to a net or a
// concatenation of nets and never to a variable, and a select or a
// concatenation reaches a variable as surely as its bare name does: each form
// that names one is reported as the bare variable is, named or positional.
TEST(PortConnectionRulesForNetsElaboration,
     VariableReachedThroughASelectOrConcatenationOnInoutErrors) {
  const char* const kConnections[] = {
      ".a(v[1])",         ".a(v[2:1])",       ".a(v[1 +: 2])", ".a(v[3 -: 2])",
      ".a({w[0], v[1]})", ".a({v[0], w[1]})", "{w[0], v[1]}"};
  for (const char* connection : kConnections) {
    ElabFixture f;
    ElaborateSrc(InoutConnectedTo(connection), f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "variable 'v' cannot be connected to inout "
                              "port 'a'",
                              7, "23.3.3.3"))
        << connection;
  }
}

// A bare variable among a concatenation's parts is the variable itself.
TEST(PortConnectionRulesForNetsElaboration,
     BareVariableInAConcatenationOnInoutErrors) {
  ElabFixture f;
  ElaborateSrc(InoutConnectedTo(".a({b, w[0]})"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'b' cannot be connected to inout port "
                            "'a'",
                            7, "23.3.3.3"));
}

// The same forms reaching nets alone are what §23.3.3.3 permits.
TEST(PortConnectionRulesForNetsElaboration,
     NetReachedThroughASelectOrConcatenationOnInoutIsAccepted) {
  const char* const kConnections[] = {".a(w[1])",         ".a(w[2:1])",
                                      ".a(w[1 +: 2])",    ".a(w[3 -: 2])",
                                      ".a({w[0], n[1]})", "{n[0], w[1]}"};
  for (const char* connection : kConnections) {
    EXPECT_TRUE(ElabOk(InoutConnectedTo(connection))) << connection;
  }
}

}  // namespace
