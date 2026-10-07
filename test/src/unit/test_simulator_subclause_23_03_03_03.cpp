
#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PortConnectionRulesForNetsSimulation,
     InputNetPortReceivesValueFromParent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input wire [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] drv = 8'h42;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(drv), .b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x42u);
}

TEST(PortConnectionRulesForNetsSimulation,
     UnconnectedInputNetPortProducesHighZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input wire [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0x00u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(PortConnectionRulesForNetsSimulation,
     InputNetPortConnectedToExpressionReceivesComputedValue) {
  // An input net port accepts any expression, not just a bare signal; the
  // simulator evaluates the connection expression and drives the port with
  // its computed value.
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input wire [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] drv = 8'h40;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(drv + 8'd2), .b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x42u);
}

TEST(PortConnectionRulesForNetsSimulation, OutputNetPortDrivesParentVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(output wire [7:0] y);\n"
      "  assign y = 8'h55;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.y(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x55u);
}

TEST(PortConnectionRulesForNetsSimulation, OutputNetPortDrivesParentNet) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(output wire [7:0] y);\n"
      "  assign y = 8'hBE;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  child u(.y(bus));\n"
      "endmodule\n",
      f, "bus");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBEu);
}

TEST(PortConnectionRulesForNetsSimulation,
     InputNetPortConnectedToParameterReceivesValue) {
  // An input net port accepts any compatible expression, including a constant
  // parameter reference. Built from a real parameter declaration and driven
  // end-to-end, the elaborated constant reaches the port and its sink.
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input wire [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  parameter logic [7:0] P = 8'h6D;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(P), .b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x6Du);
}

TEST(PortConnectionRulesForNetsSimulation,
     InputNetPortConnectedToLocalparamReceivesValue) {
  // A localparam constant is likewise carried across an input net port
  // connection to its sink when driven through the full pipeline.
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input wire [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  localparam logic [7:0] L = 8'h2E;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(L), .b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x2Eu);
}

TEST(PortConnectionRulesForNetsSimulation,
     InoutNetPortPropagatesValueToParent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(inout wire [7:0] data);\n"
      "  assign data = 8'hCD;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  child u(.data(bus));\n"
      "endmodule\n",
      f, "bus");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

// §23.3.3.3 connects an inout net port to a net, and §23.3.3.7 merges the
// port's net and the connected net into one simulated net, so a continuous
// assignment inside the child is one driver of the parent's net beside the
// parent's own, and §6.6.1's wire resolution combines the two: the parent
// drives the low nibble and leaves the high one at z, the child the reverse.
// Written directly into the shared variable rather than joining the drivers,
// the child's value would stand alone as 8'hFz or be overwritten by the
// parent's 8'hz0; only the resolved 8'hF0 says both drivers reached the net.
TEST(PortConnectionRulesForNetsSimulation,
     InoutNetPortDriverResolvesWithParentDriver) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(inout wire [7:0] data);\n"
      "  assign data = 8'b1111_zzzz;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  assign bus = 8'bzzzz_0000;\n"
      "  child u(.data(bus));\n"
      "endmodule\n",
      f, "bus");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xF0u);
}

// §23.3.3.3 (printed page 747) with §9.4.2: an event control on a net wakes on
// a change of its value, and a net whose driver resolves to the z it already
// holds has not changed. The issue's probes -- the net driven through a
// program's inout port (66) and a module's (66b) by `assign data = drv` with
// drv z until 2 -- and the same net through an explicit and an implicit output
// net port, and driven in the module itself, each wake only at 2. Each woke at
// time 0 too, `data=z at 0`: the net's first z carried set bits above its
// width, and an output net port started at 0 or x, which its connection copied
// up before the port's own driver ran.
TEST(PortConnectionRulesForNetsSimulation, NetDrivenToTheZItHoldsDoesNotWake) {
  const char* const kDrivers[] = {
      "program p(inout wire [7:0] data);\n"
      "  logic [7:0] drv = 8'bz;\n"
      "  assign data = drv;\n"
      "  initial begin #2 drv = 8'hAA; #1; end\n"
      "endprogram\n",
      "module p(inout wire [7:0] data);\n"
      "  logic [7:0] drv = 8'bz;\n"
      "  assign data = drv;\n"
      "  initial begin #2 drv = 8'hAA; #1; end\n"
      "endmodule\n",
      "module p(output wire [7:0] data);\n"
      "  logic [7:0] drv = 8'bz;\n"
      "  assign data = drv;\n"
      "  initial begin #2 drv = 8'hAA; #1; end\n"
      "endmodule\n",
      "module p(output [7:0] data);\n"
      "  logic [7:0] drv = 8'bz;\n"
      "  assign data = drv;\n"
      "  initial begin #2 drv = 8'hAA; #1; end\n"
      "endmodule\n"};
  for (const char* driver : kDrivers) {
    SimFixture f;
    EXPECT_EQ(RunCapture(std::string(driver) +
                             "module top;\n"
                             "  wire [7:0] data;\n"
                             "  p pi(data);\n"
                             "  always @(data) $display(\"data=%0d at %0t\", "
                             "data, $time);\n"
                             "endmodule\n",
                         f),
              "data=170 at 2\n")
        << driver;
  }
  SimFixture g;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  wire [7:0] data;\n"
                       "  wire b;\n"
                       "  logic [7:0] d = 8'bz;\n"
                       "  assign data = d;\n"
                       "  assign b = 1'bz;\n"
                       "  always @(data) $display(\"data=%0d at %0t\", data, "
                       "$time);\n"
                       "  always @(b) $display(\"b at %0t\", $time);\n"
                       "  initial #2 d = 8'hAA;\n"
                       "endmodule\n",
                       g),
            "data=170 at 2\n");
}

// §23.3.3.3: a net port is a net, and one left unconnected has the value z --
// an explicit `input wire` and an implicit `input` read z, and an output net
// port its own drivers leave undriven gives the net above z -- where a variable
// port (§23.3.3.2) reads its type's default x. The explicit `output wire` port
// read 0 before its drivers ran.
TEST(PortConnectionRulesForNetsSimulation, NetPortsStartAtHighZ) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub(input wire [3:0] i, input var logic [3:0] "
                       "vi,\n"
                       "           input [3:0] ii, output wire [3:0] ow);\n"
                       "  initial $display(\"i=%b vi=%b ii=%b ow=%b\", i, vi, "
                       "ii, ow);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  wire [3:0] o;\n"
                       "  sub s(.i(), .vi(), .ii(), .ow(o));\n"
                       "  initial #1 $display(\"o=%b\", o);\n"
                       "endmodule\n",
                       f),
            "i=zzzz vi=xxxx ii=zzzz ow=zzzz\no=zzzz\n");
}

// §23.3.3.3 with §23.2.2.3: `input logic a`, which names a data type and no
// port kind, is a net of the default net type, so left unconnected, whether
// off the list or as `.a()`, it reads z as a declared wire does, beside the
// tri0 and tri1 nets that pull to 0 and 1. Its data type keyword was read as
// making it a variable, and it read x.
TEST(PortConnectionRulesForNetsSimulation,
     AnInputNamingOnlyADataTypeIsANetReadingHighZ) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub(input logic a, output logic b);\n"
                       "  assign b = a;\n"
                       "endmodule\n"
                       "module t;\n"
                       "  logic b, e;\n"
                       "  tri0 n0;\n"
                       "  tri1 n1;\n"
                       "  wire nw;\n"
                       "  sub s(.b(b));\n"
                       "  sub s2(.a(), .b(e));\n"
                       "  initial #1 $display(\"unconnected=%b empty=%b "
                       "tri0=%b tri1=%b wire=%b\", b, e, n0, n1, nw);\n"
                       "endmodule\n",
                       f),
            "unconnected=z empty=z tri0=0 tri1=1 wire=z\n");
}

}  // namespace
