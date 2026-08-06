#include <gtest/gtest.h>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "helpers_logic4vec_z.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(NetTypesIntro, WireValueFollowsSingleDriver) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x5A));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0x5Au);
}

TEST(NetTypesIntro, WireWithAllZDriversResolvesToZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 4, 0xA);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeZVec(arena, 4));
  net.drivers.push_back(MakeZVec(arena, 4));

  net.Resolve(arena);
  EXPECT_TRUE(IsAllZ(var->value));
}

TEST(NetTypesIntro, WireDoesNotStoreValueWhenDriversReturnToZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xC3));

  net.Resolve(arena);
  ASSERT_EQ(var->value.ToUint64(), 0xC3u);

  net.drivers[0] = MakeZVec(arena, 8);
  net.Resolve(arena);
  EXPECT_TRUE(IsAllZ(var->value));
}

TEST(NetTypesIntro, TriregRetainsValueWhenAllDriversGoToZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x7E));

  net.Resolve(arena);
  ASSERT_EQ(var->value.ToUint64(), 0x7Eu);

  net.drivers[0] = MakeZVec(arena, 8);
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0x7Eu);
}

TEST(NetTypesIntro, WireWithMultipleDriversCombinesValues) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 4);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b0001));
  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b0001));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64() & 0xFu, 0b0001u);
}

TEST(NetTypesIntro, UndrivenBuiltinNetInitializesToZ) {
  SimFixture f;
  auto* net = f.ctx.CreateNet("w", NetType::kWire, 8);
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  EXPECT_TRUE(net->drivers.empty());
  EXPECT_TRUE(IsAllZ(net->resolved->value));
}

TEST(NetTypesIntro, WandDoesNotStoreValueWhenDriversReturnToZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xFF));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xFF));

  net.Resolve(arena);
  ASSERT_EQ(var->value.ToUint64() & 0xFFu, 0xFFu);

  net.drivers[0] = MakeZVec(arena, 8);
  net.drivers[1] = MakeZVec(arena, 8);
  net.Resolve(arena);
  EXPECT_TRUE(IsAllZ(var->value));
}

// §6.6: a net does not store a value; its value is determined by its drivers.
// Driven end to end from real declaration syntax: a tri-state buffer whose
// enable is high forces the wire to follow the driven data value.
TEST(NetTypesIntro, WireValueFollowsActiveDriverFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg dat, en;\n"
      "  wire y;\n"
      "  bufif1 g(y, dat, en);\n"
      "  initial begin dat = 1'b1; en = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);  // logic 1
  EXPECT_EQ(w.bval & 1u, 0u);
}

// §6.6 names a continuous assignment as one of the driver kinds that determine
// a net's value (the other being a gate, covered above). End-to-end from §10.3
// source syntax: an `assign` drives the wire and its value follows the RHS.
TEST(NetTypesIntro, WireValueDeterminedByContinuousAssignFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  assign y = a & b;\n"
      "  initial begin a = 1'b1; b = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);  // 1 & 1 = 1
  EXPECT_EQ(w.bval & 1u, 0u);
}

// §6.6: a net with no driver connected at all shall hold high impedance (z).
// Purest form: a wire that is declared but never driven by any construct.
TEST(NetTypesIntro, NeverDrivenWireIsHighZFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y;\n"  // declared, no driver anywhere
      "  reg r;\n"
      "  initial r = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 0u);  // z = (aval=0, bval=1)
  EXPECT_EQ(w.bval & 1u, 1u);
}

// §6.6: when no driver is connected to a (non-trireg) net, its value shall be
// high impedance (z) — the net holds nothing of its own. Driven from source: a
// tri-state buffer that was driving the wire is disabled, leaving it undriven.
TEST(NetTypesIntro, UndrivenWireGoesToZFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg dat, en;\n"
      "  wire y;\n"
      "  bufif1 g(y, dat, en);\n"
      "  initial begin dat = 1'b1; en = 1'b1; #5 en = 1'b0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 0u);  // z = (aval=0, bval=1)
  EXPECT_EQ(w.bval & 1u, 1u);
}

TEST(NetTypesIntro, TriregFollowsRemainingDriverWhenOneOfTwoGoesToZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x33));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x33));

  net.Resolve(arena);
  ASSERT_EQ(var->value.ToUint64() & 0xFFu, 0x33u);

  net.drivers[0] = MakeZVec(arena, 8);
  net.drivers[1] = MakeLogic4VecVal(arena, 8, 0x55);
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64() & 0xFFu, 0x55u);
}

}  // namespace
