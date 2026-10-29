#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <string>
#include <string_view>

#include "common/types.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(UwireElaboration, UwireNetType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  uwire uw;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].name, "uw");
  EXPECT_EQ(mod->nets[0].net_type, NetType::kUwire);
}

TEST(UwireElaboration, UwireSingleContinuousAssignmentOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  uwire w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The report stands at the second continuous assignment, which is the one that
// finds `w` already driven.
TEST(UwireElaboration, UwireMultipleContinuousAssignmentsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  uwire w;\n"
      "  assign w = 1'b0;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "uwire 'w' cannot have multiple drivers", 4,
                            "6.6.2"));
}

TEST(UwireElaboration, UwireNetDeclAssignPlusContinuousAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  uwire w = 1'b0;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "uwire 'w' cannot have multiple drivers", 3,
                            "6.6.2"));
}

TEST(UwireElaboration, MultipleContinuousAssignmentsOnPlainWireOk) {
  // The single-driver restriction is specific to uwire: an ordinary wire
  // resolves multiple drivers, so two continuous assignments are not an error.
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1'b0;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(UwireElaboration, UwireOnBidirectionalSwitchTerminalError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  uwire a;\n"
      "  wire b;\n"
      "  tran sw(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "uwire net cannot connect to a bidirectional "
                            "terminal of a bidirectional pass switch",
                            4, "6.6.2"));
}

TEST(UwireElaboration, UwireOnSecondBidirectionalTerminalError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire a;\n"
      "  uwire b;\n"
      "  wire ctrl;\n"
      "  tranif1 sw(a, b, ctrl);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "uwire net cannot connect to a bidirectional "
                            "terminal of a bidirectional pass switch",
                            5, "6.6.2"));
}

TEST(UwireElaboration, UwireBitSelectOnBidirectionalTerminalError) {
  // Connecting a single bit of a uwire net to a bidirectional terminal is
  // still connecting (a bit of) a uwire net, so it is an error.
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  uwire [1:0] u;\n"
      "  wire w;\n"
      "  tran sw(u[0], w);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "uwire net cannot connect to a bidirectional "
                            "terminal of a bidirectional pass switch",
                            4, "6.6.2"));
}

TEST(UwireElaboration, UwireOnResistiveBidirectionalSwitchTerminalError) {
  // The restriction applies to every bidirectional pass switch variant,
  // including the resistive rtran.
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  uwire a;\n"
      "  wire b;\n"
      "  rtran sw(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "uwire net cannot connect to a bidirectional "
                            "terminal of a bidirectional pass switch",
                            4, "6.6.2"));
}

TEST(UwireElaboration, UwireOnEnableLowControlSwitchTerminalError) {
  // The restriction applies to the enable-low control switch tranif0; a uwire
  // on either of its two bidirectional terminals is an error.
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  uwire a;\n"
      "  wire b;\n"
      "  wire ctrl;\n"
      "  tranif0 sw(a, b, ctrl);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "uwire net cannot connect to a bidirectional "
                            "terminal of a bidirectional pass switch",
                            5, "6.6.2"));
}

TEST(UwireElaboration, UwireOnResistiveEnableLowControlSwitchTerminalError) {
  // rtranif0 is the resistive enable-low control bidirectional pass switch;
  // the second bidirectional terminal here carries the uwire.
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire a;\n"
      "  uwire b;\n"
      "  wire ctrl;\n"
      "  rtranif0 sw(a, b, ctrl);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "uwire net cannot connect to a bidirectional "
                            "terminal of a bidirectional pass switch",
                            5, "6.6.2"));
}

TEST(UwireElaboration, UwireOnResistiveEnableHighControlSwitchTerminalError) {
  // rtranif1 is the resistive enable-high control bidirectional pass switch.
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  uwire a;\n"
      "  wire b;\n"
      "  wire ctrl;\n"
      "  rtranif1 sw(a, b, ctrl);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "uwire net cannot connect to a bidirectional "
                            "terminal of a bidirectional pass switch",
                            5, "6.6.2"));
}

TEST(UwireElaboration, PlainWireOnBidirectionalSwitchTerminalOk) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire a;\n"
      "  wire b;\n"
      "  tran sw(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(UwireElaboration, UwireVectorWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  uwire [3:0] bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].width, 4u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kUwire);
}

// §6.6.2: the report that rejects a second driver on a uwire net names the
// subclause stating the single-driver rule, so a caller learns which rule was
// enforced without matching the wording of the message.
TEST(UwireElaboration, MultipleContinuousAssignmentsNames6_6_2) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  uwire w;\n"
      "  assign w = 1'b0;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "uwire 'w' cannot have multiple drivers", 4,
                            "6.6.2"));
}

// §6.6.2 makes it an error to connect any bit of a uwire net to more than one
// driver, whatever the drivers are. The report stands at the driver that
// finds the bit already driven.
::testing::AssertionResult UwireReported(const std::string& src,
                                         std::string_view name, uint32_t line) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return ReportedError(
      f.diag.Diagnostics(),
      std::format("uwire '{}' cannot have multiple drivers", name), line,
      "6.6.2");
}

// A gate's output drives the net as a continuous assignment does: beside an
// assignment, and beside a second gate, it is a second driver.
TEST(UwireElaboration, GateOutputIsADriver) {
  EXPECT_TRUE(
      UwireReported("module t(input logic a, b);\n"
                    "  uwire u;\n"
                    "  buf (u, a);\n"
                    "  assign u = b;\n"
                    "endmodule\n",
                    "u", 4));
  EXPECT_TRUE(
      UwireReported("module t(input logic a, b);\n"
                    "  uwire u;\n"
                    "  buf (u, a);\n"
                    "  not (u, b);\n"
                    "endmodule\n",
                    "u", 4));
  EXPECT_TRUE(
      ElabOk("module t(input logic a);\n"
             "  uwire u;\n"
             "  buf (u, a);\n"
             "endmodule\n"));
}

// A UDP's output is a driver the same way.
TEST(UwireElaboration, UdpOutputIsADriver) {
  const std::string kUdp =
      "primitive inv(output o, input i);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n";
  EXPECT_TRUE(UwireReported(kUdp + "module t(input logic a, b);\n"
                                   "  uwire u;\n"
                                   "  inv g(u, a);\n"
                                   "  assign u = b;\n"
                                   "endmodule\n",
                            "u", 10));
  EXPECT_TRUE(ElabOk(kUdp + "module t(input logic a);\n"
                            "  uwire u;\n"
                            "  inv g(u, a);\n"
                            "endmodule\n"));
}

// A unidirectional switch's output, and a pull gate's, drive the net too.
TEST(UwireElaboration, SwitchAndPullOutputsAreDrivers) {
  EXPECT_TRUE(
      UwireReported("module t(input logic d, g, b);\n"
                    "  uwire u;\n"
                    "  nmos (u, d, g);\n"
                    "  assign u = b;\n"
                    "endmodule\n",
                    "u", 4));
  EXPECT_TRUE(
      UwireReported("module t(input logic b);\n"
                    "  uwire u;\n"
                    "  pullup (u);\n"
                    "  assign u = b;\n"
                    "endmodule\n",
                    "u", 4));
  EXPECT_TRUE(
      ElabOk("module t(input logic d, g);\n"
             "  uwire u;\n"
             "  nmos (u, d, g);\n"
             "endmodule\n"));
}

// The rule is stated of each bit: drivers of different bits of a uwire vector
// are each the only driver of their bit, and two drivers reaching one bit,
// through bit-selects, part-selects, indexed part-selects, the whole vector
// or a concatenation, are reported.
TEST(UwireElaboration, DriversOfOneBitThroughSelectsAreReported) {
  const std::string kHead =
      "module t(input logic [3:0] a, b);\n"
      "  uwire [3:0] u;\n";
  EXPECT_TRUE(UwireReported(kHead + "  assign u[0] = a[0];\n"
                                    "  assign u[0] = b[0];\n"
                                    "endmodule\n",
                            "u", 4));
  EXPECT_TRUE(UwireReported(kHead + "  assign u[2:0] = a[2:0];\n"
                                    "  assign u[3:2] = b[1:0];\n"
                                    "endmodule\n",
                            "u", 4));
  EXPECT_TRUE(UwireReported(kHead + "  assign u[0 +: 2] = a[1:0];\n"
                                    "  assign u[2 -: 2] = b[1:0];\n"
                                    "endmodule\n",
                            "u", 4));
  EXPECT_TRUE(UwireReported(kHead + "  assign u = a;\n"
                                    "  assign u[1] = b[1];\n"
                                    "endmodule\n",
                            "u", 4));
  EXPECT_TRUE(UwireReported(kHead + "  assign {u[3], u[0]} = a[1:0];\n"
                                    "  assign u[0] = b[0];\n"
                                    "endmodule\n",
                            "u", 4));
}

TEST(UwireElaboration, DriversOfDifferentBitsAreAccepted) {
  EXPECT_TRUE(
      ElabOk("module t(input logic [3:0] a, b);\n"
             "  uwire [3:0] u;\n"
             "  assign u[0] = a[0];\n"
             "  assign u[1] = b[1];\n"
             "  assign u[3:2] = a[3:2];\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module t(input logic [3:0] a, b);\n"
             "  uwire [3:0] u;\n"
             "  assign u[0 +: 2] = a[1:0];\n"
             "  assign u[3 -: 2] = b[1:0];\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module t(input logic [3:0] a, b);\n"
             "  uwire [3:0] u;\n"
             "  assign {u[3], u[0]} = a[1:0];\n"
             "  assign {u[2], u[1]} = b[1:0];\n"
             "endmodule\n"));
}

// A gate's output on one bit drives that bit alone.
TEST(UwireElaboration, GateOutputOnOneBitDrivesThatBit) {
  EXPECT_TRUE(
      UwireReported("module t(input logic a, b);\n"
                    "  uwire [3:0] u;\n"
                    "  buf (u[1], a);\n"
                    "  assign u[1] = b;\n"
                    "endmodule\n",
                    "u", 4));
  EXPECT_TRUE(
      ElabOk("module t(input logic a, b);\n"
             "  uwire [3:0] u;\n"
             "  buf (u[1], a);\n"
             "  assign u[0] = b;\n"
             "endmodule\n"));
}

// Elements of an array of uwire vectors are distinct nets, each driven once.
TEST(UwireElaboration, ElementsOfAUwireArrayAreDrivenApart) {
  EXPECT_TRUE(
      ElabOk("module t(input logic a, b);\n"
             "  uwire [3:0] u [2];\n"
             "  assign u[0][1] = a;\n"
             "  assign u[1][0] = b;\n"
             "endmodule\n"));
}

// The rule holds in an interface and a program as in a module; a program
// takes no gate (§24.3), so its second driver is a declaration assignment.
TEST(UwireElaboration, InterfaceAndProgramUwireDrivers) {
  EXPECT_TRUE(
      UwireReported("interface i;\n"
                    "  uwire u;\n"
                    "  assign u = 1'b0;\n"
                    "  assign u = 1'b1;\n"
                    "endinterface\n"
                    "module t;\n"
                    "  i x();\n"
                    "endmodule\n",
                    "u", 4));
  EXPECT_TRUE(
      UwireReported("program p;\n"
                    "  uwire u = 1'b0;\n"
                    "  assign u = 1'b1;\n"
                    "endprogram\n"
                    "module t;\n"
                    "  p x();\n"
                    "endmodule\n",
                    "u", 3));
  EXPECT_TRUE(
      ElabOk("interface i;\n"
             "  uwire [1:0] u;\n"
             "  assign u[0] = 1'b0;\n"
             "  assign u[1] = 1'b1;\n"
             "endinterface\n"
             "module t;\n"
             "  i x();\n"
             "endmodule\n"));
}

// A uwire port is a uwire net of its module, written in the ANSI header or
// in a non-ANSI port declaration.
TEST(UwireElaboration, UwirePortDrivers) {
  EXPECT_TRUE(
      UwireReported("module t(output uwire u, input logic a, b);\n"
                    "  assign u = a;\n"
                    "  assign u = b;\n"
                    "endmodule\n",
                    "u", 3));
  EXPECT_TRUE(
      UwireReported("module t(u, a, b);\n"
                    "  output uwire u;\n"
                    "  input logic a, b;\n"
                    "  buf (u, a);\n"
                    "  assign u = b;\n"
                    "endmodule\n",
                    "u", 5));
  EXPECT_TRUE(
      ElabOk("module t(output uwire [1:0] u, input logic a, b);\n"
             "  assign u[0] = a;\n"
             "  assign u[1] = b;\n"
             "endmodule\n"));
}

// Under `default_nettype uwire an implicit net is a uwire net, whether the
// left-hand side of a continuous assignment or a gate's terminal declares it.
TEST(UwireElaboration, ImplicitUwireNetDrivers) {
  EXPECT_TRUE(
      UwireReported("`default_nettype uwire\n"
                    "module t(input logic a, b);\n"
                    "  assign x = a;\n"
                    "  assign x = b;\n"
                    "endmodule\n"
                    "`default_nettype wire\n",
                    "x", 4));
  EXPECT_TRUE(
      UwireReported("`default_nettype uwire\n"
                    "module t(input logic a, b);\n"
                    "  buf (y, a);\n"
                    "  buf (y, b);\n"
                    "endmodule\n"
                    "`default_nettype wire\n",
                    "y", 4));
  EXPECT_TRUE(
      ElabOk("`default_nettype uwire\n"
             "module t(input logic a);\n"
             "  assign x = a;\n"
             "endmodule\n"
             "`default_nettype wire\n"));
}

// An array of instances connects a terminal as wide as the array one bit to
// each instance, and any other terminal whole to every instance, so each
// instance drives it (§28.3.6).
TEST(UwireElaboration, InstanceArrayTerminalDrivers) {
  EXPECT_TRUE(
      UwireReported("module t(input logic [1:0] a);\n"
                    "  uwire u;\n"
                    "  buf b[1:0] (u, a);\n"
                    "endmodule\n",
                    "u", 3));
  EXPECT_TRUE(
      UwireReported("module t(input logic [1:0] a);\n"
                    "  uwire [1:0] u;\n"
                    "  buf b[1:0] (u, a);\n"
                    "  assign u[1] = 1'b0;\n"
                    "endmodule\n",
                    "u", 4));
  EXPECT_TRUE(
      ElabOk("module t(input logic [1:0] a);\n"
             "  uwire [1:0] u;\n"
             "  buf b[1:0] (u, a);\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module t(input logic [1:0] a);\n"
             "  uwire u;\n"
             "  buf b[0:0] (u, a[0]);\n"
             "endmodule\n"));
}

// A member of a uwire net of a packed structure is the bits of that member: two
// members are driven apart, and the whole net and one member meet.
TEST(UwireElaboration, StructureMemberDrivers) {
  const std::string kHead =
      "module t(input logic a, b);\n"
      "  uwire struct packed { logic x; logic y; } s;\n";
  EXPECT_TRUE(UwireReported(kHead + "  assign s.x = a;\n"
                                    "  assign s = {a, b};\n"
                                    "endmodule\n",
                            "s", 4));
  EXPECT_TRUE(UwireReported(kHead + "  assign s.y = a;\n"
                                    "  assign s.y = b;\n"
                                    "endmodule\n",
                            "s", 4));
  EXPECT_TRUE(ElabOk(kHead + "  assign s.x = a;\n"
                             "  assign s.y = b;\n"
                             "endmodule\n"));
}

// Selects of several dimensions name bits down each of them: a select of an
// outer dimension reaches every bit beneath it.
TEST(UwireElaboration, MultidimensionalSelectDrivers) {
  EXPECT_TRUE(
      UwireReported("module t(input logic [3:0] a, input logic b);\n"
                    "  uwire [1:0][3:0] u;\n"
                    "  assign u[1][2] = b;\n"
                    "  assign u[1] = a;\n"
                    "endmodule\n",
                    "u", 4));
  EXPECT_TRUE(
      UwireReported("module t(input logic [3:0] a, input logic b);\n"
                    "  uwire [3:0] u [2];\n"
                    "  assign u[0] = a;\n"
                    "  assign u[0][1] = b;\n"
                    "endmodule\n",
                    "u", 4));
  EXPECT_TRUE(
      ElabOk("module t(input logic [3:0] a, input logic b);\n"
             "  uwire [1:0][3:0] u;\n"
             "  assign u[1][2] = b;\n"
             "  assign u[1][3] = b;\n"
             "  assign u[0] = a;\n"
             "endmodule\n"));
}

// A generate block's own uwire net takes one driver, and a module's uwire net
// driven from a loop generate block is driven once by each iteration: two
// iterations driving one bit are two drivers, and each driving its own bit
// is one.
TEST(UwireElaboration, GenerateBlockUwireDrivers) {
  EXPECT_TRUE(
      UwireReported("module t(input logic a, b);\n"
                    "  if (1) begin : g\n"
                    "    uwire u;\n"
                    "    assign u = a;\n"
                    "    assign u = b;\n"
                    "  end\n"
                    "endmodule\n",
                    "u", 5));
  EXPECT_TRUE(
      UwireReported("module t;\n"
                    "  uwire [1:0] u;\n"
                    "  for (genvar i = 0; i < 2; i++) begin : g\n"
                    "    assign u[0] = 1'b0;\n"
                    "  end\n"
                    "endmodule\n",
                    "u", 4));
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  uwire [1:0] u;\n"
             "  for (genvar i = 0; i < 2; i++) begin : g\n"
             "    assign u[i] = 1'b0;\n"
             "  end\n"
             "endmodule\n"));
}

// A uwire net the compilation unit declares is driven by the modules of the
// design: by two assignments of one module, by two modules, and by two
// instances of one module. §3.12.1 gives the unit no net declaration
// assignment, so its net has no driver of its own.
TEST(UwireElaboration, CompilationUnitUwireDrivers) {
  EXPECT_TRUE(
      UwireReported("uwire w;\n"
                    "module t;\n"
                    "  assign w = 1'b0;\n"
                    "  assign w = 1'b1;\n"
                    "endmodule\n",
                    "w", 4));
  EXPECT_TRUE(
      UwireReported("uwire w;\n"
                    "module m;\n"
                    "  assign w = 1'b0;\n"
                    "endmodule\n"
                    "module n;\n"
                    "  assign w = 1'b1;\n"
                    "endmodule\n"
                    "module t;\n"
                    "  m x();\n"
                    "  n y();\n"
                    "endmodule\n",
                    "w", 6));
  EXPECT_TRUE(
      UwireReported("uwire w;\n"
                    "module m;\n"
                    "  assign w = 1'b0;\n"
                    "endmodule\n"
                    "module t;\n"
                    "  m x();\n"
                    "  m y();\n"
                    "endmodule\n",
                    "w", 3));
  EXPECT_TRUE(
      ElabOk("uwire [1:0] w;\n"
             "module m;\n"
             "  assign w[0] = 1'b0;\n"
             "endmodule\n"
             "module n;\n"
             "  assign w[1] = 1'b1;\n"
             "endmodule\n"
             "module t;\n"
             "  m x();\n"
             "  n y();\n"
             "endmodule\n"));
}

// Each element of an array of instances is an instance of its own (§23.3.2),
// so a module that drives a unit's uwire net once drives it once per element.
TEST(UwireElaboration, InstanceArrayDrivesAUnitUwireOncePerElement) {
  const std::string kUnit =
      "uwire w;\n"
      "module m;\n"
      "  assign w = 1'b0;\n"
      "endmodule\n";
  EXPECT_TRUE(UwireReported(kUnit + "module t;\n"
                                    "  m x[1:0] ();\n"
                                    "endmodule\n",
                            "w", 6));
  EXPECT_TRUE(ElabOk(kUnit + "module t;\n"
                             "  m x[0:0] ();\n"
                             "endmodule\n"));
}

// A module's own object of the unit uwire net's name is that object, so its
// drivers are not the unit net's: a port and a net of the module.
TEST(UwireElaboration, LocalObjectHidesCompilationUnitUwire) {
  const std::string kUnit =
      "uwire w;\n"
      "module m;\n"
      "  assign w = 1'b0;\n"
      "endmodule\n";
  EXPECT_TRUE(ElabOk(kUnit + "module t(output wire w);\n"
                             "  assign w = 1'b1;\n"
                             "  m x();\n"
                             "endmodule\n"));
  EXPECT_TRUE(ElabOk(kUnit + "module t;\n"
                             "  wire w;\n"
                             "  assign w = 1'b1;\n"
                             "  m x();\n"
                             "endmodule\n"));
}

// A select that is not constant names no bit, and Table 10-1 reports it; it
// is counted as the driver of no bit.
TEST(UwireElaboration, NonConstantSelectDrivesNoCountedBit) {
  ElabFixture f;
  ElaborateSrc(
      "module t(input logic a, b);\n"
      "  uwire [3:0] u;\n"
      "  int k;\n"
      "  assign u[k] = a;\n"
      "  assign u[1:k] = b;\n"
      "  assign u[1] = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "continuous assignment left-hand side requires a "
                            "constant select expression",
                            4, "10.3.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "uwire 'u' cannot have multiple drivers", 6,
                             "6.6.2"));
}

}  // namespace
