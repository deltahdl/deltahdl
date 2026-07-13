#include <gtest/gtest.h>

#include "common/arena.h"
#include "helpers_scheduler.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(WireTriResolution, Wire_0_0) {
  Logic4Word a{0, 0};
  Logic4Word b{0, 0};
  auto r = ResolveWireWord(a, b);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WireTriResolution, Wire_0_1) {
  Logic4Word a{0, 0};
  Logic4Word b{1, 0};
  auto r = ResolveWireWord(a, b);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_0_x) {
  Logic4Word zero{0, 0};
  Logic4Word x{1, 1};
  auto r = ResolveWireWord(zero, x);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_0_z) {
  Logic4Word zero{0, 0};
  Logic4Word z{0, 1};
  auto r = ResolveWireWord(zero, z);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WireTriResolution, Wire_1_0) {
  Logic4Word one{1, 0};
  Logic4Word zero{0, 0};
  auto r = ResolveWireWord(one, zero);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_1_1) {
  Logic4Word a{1, 0};
  Logic4Word b{1, 0};
  auto r = ResolveWireWord(a, b);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WireTriResolution, Wire_1_x) {
  Logic4Word one{1, 0};
  Logic4Word x{1, 1};
  auto r = ResolveWireWord(one, x);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_1_z) {
  Logic4Word one{1, 0};
  Logic4Word z{0, 1};
  auto r = ResolveWireWord(one, z);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WireTriResolution, Wire_x_0) {
  Logic4Word x{1, 1};
  Logic4Word zero{0, 0};
  auto r = ResolveWireWord(x, zero);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_x_1) {
  Logic4Word x{1, 1};
  Logic4Word one{1, 0};
  auto r = ResolveWireWord(x, one);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_x_x) {
  Logic4Word x{1, 1};
  auto r = ResolveWireWord(x, x);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_x_z) {
  Logic4Word x{1, 1};
  Logic4Word z{0, 1};
  auto r = ResolveWireWord(x, z);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_z_0) {
  Logic4Word z{0, 1};
  Logic4Word zero{0, 0};
  auto r = ResolveWireWord(z, zero);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WireTriResolution, Wire_z_1) {
  Logic4Word z{0, 1};
  Logic4Word one{1, 0};
  auto r = ResolveWireWord(z, one);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WireTriResolution, Wire_z_x) {
  Logic4Word z{0, 1};
  Logic4Word x{1, 1};
  auto r = ResolveWireWord(z, x);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_z_z) {
  Logic4Word z{0, 1};
  auto r = ResolveWireWord(z, z);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, ResolveSingleDriverWire) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 42));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(WireTriResolution, ResolveMultipleDriversAgreeWire) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 7));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 7));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(WireTriResolution, ResolveMultipleDriversConflictWire) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xF0));

  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xFFu);  // all bits x = (1, 1)
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(WireTriResolution, ResolveEmptyDriversNoChange) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 99);
  Net net;
  net.resolved = var;

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(WireTriResolution, TriUsesWireResolution) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 7));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 7));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(WireTriResolution, TriConflictProducesX) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xF0));

  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xFFu);  // all bits x = (1, 1)
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(WireTriResolution, TriSingleDriver) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xAB));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(WireTriResolution, ThreeDriverWireResolution) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 4);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b0011));
  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b0101));
  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b0001));

  net.Resolve(arena);

  auto w = var->value.words[0];

  EXPECT_TRUE((w.aval & 1u) != 0);
  EXPECT_TRUE((w.bval & 1u) == 0);

  // bit1 and bit2 resolve to x; Convention A sets aval on an x bit.
  EXPECT_TRUE((w.aval & 2u) != 0);
  EXPECT_TRUE((w.bval & 2u) != 0);

  EXPECT_TRUE((w.aval & 4u) != 0);
  EXPECT_TRUE((w.bval & 4u) != 0);

  EXPECT_TRUE((w.aval & 8u) == 0);
  EXPECT_TRUE((w.bval & 8u) == 0);
}

TEST(WireTriResolution, WireZDriverPassesThrough) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 42));
  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = 0x00;  // z = (aval=0, bval=1) per Convention A
  z_drv.words[0].bval = 0xFF;
  net.drivers.push_back(z_drv);

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(WireTriResolution, TriZDriverPassesThrough) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 42));
  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = 0x00;  // z = (aval=0, bval=1) per Convention A
  z_drv.words[0].bval = 0xFF;
  net.drivers.push_back(z_drv);

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// --- Real-source, full-pipeline observation of §6.6.1 ---
//
// The synthetic cases above pin ResolveWireWord and Net::Resolve against
// Table 6-2 directly. The behavior the LRM defines, though, is about resolving
// the *multiple drivers* a net collects -- and the tri net exists precisely to
// carry several drivers -- so the input has to be built the way real source
// builds it: two continuous assignments onto one net (legal for a net, unlike
// a variable). These drive parse -> elaborate -> lower -> run and read back the
// resolved net value, exercising the production resolution path the plain
// continuous-assignment strengths take (equal strong/strong, i.e. the
// equal-strength assumption Table 6-2 is stated under).

// §6.6.1: two agreeing drivers on a wire resolve to that shared value.
TEST(WireTriResolutionE2e, WireTwoAgreeingDriversResolveToValue) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wire w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b1;\n"
                      "  assign w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.6.1: a logical conflict from two equal-strength drivers on a wire yields
// x (the 0/1 and 1/0 cells of Table 6-2).
TEST(WireTriResolutionE2e, WireConflictingDriversResolveToX) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wire w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b0;\n"
                      "  assign w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = $isunknown(w);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.6.1: wire and tri are identical in function -- the same conflicting-driver
// input resolves to x on a tri exactly as it does on a wire.
TEST(WireTriResolutionE2e, TriConflictingDriversResolveToX) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b0;\n"
                      "  assign w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = $isunknown(w);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.6.1: a tri carrying two agreeing drivers resolves to their shared value,
// matching wire behavior (the tri is the intended home for multiple drivers).
TEST(WireTriResolutionE2e, TriTwoAgreeingDriversResolveToValue) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b1;\n"
                      "  assign w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.6.1 / Table 6-2 z column: a high-impedance driver defers to a driving
// source, so the net takes the driven value rather than conflicting.
TEST(WireTriResolutionE2e, WireHighZDriverDefersToDrivenValue) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wire w;\n"
                      "  logic result;\n"
                      "  assign w = 1'bz;\n"
                      "  assign w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.6.1 identity, z column of Table 6-2 on a tri: a tri behaves exactly like a
// wire, so a high-impedance driver defers to the driving one here too.
TEST(WireTriResolutionE2e, TriHighZDriverDefersToDrivenValue) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri w;\n"
                      "  logic result;\n"
                      "  assign w = 1'bz;\n"
                      "  assign w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.6.1: Table 6-2 applies bit by bit across a vector net. Two real drivers on
// a 4-bit wire produce, per bit, an agreement (bit0: 1&1 -> 1), two conflicts
// (bit1: 1&0 -> x, bit2: 0&1 -> x), and an agreement (bit3: 0&0 -> 0). The
// whole resolved vector is matched with case equality against 0xx1, so all four
// cells
// -- including the two x results -- are checked at once.
TEST(WireTriResolutionE2e, WireVectorResolvesTable6_2PerBit) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wire [3:0] w;\n"
                      "  logic result;\n"
                      "  assign w = 4'b0011;\n"
                      "  assign w = 4'b0101;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = (w === 4'b0xx1);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.6.1 consuming §28.11: Table 6-2 is stated for equal driver strengths.
// Building both drivers from explicit drive-strength source syntax (strong on
// both, i.e. equal) exercises that assumption directly -- a strong 0 against a
// strong 1 is an equal-strength conflict, so the wire resolves to x.
TEST(WireTriResolutionE2e, WireEqualExplicitStrengthConflictIsX) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wire w;\n"
                      "  logic result;\n"
                      "  assign (strong1, strong0) w = 1'b0;\n"
                      "  assign (strong1, strong0) w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = $isunknown(w);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

}  // namespace
