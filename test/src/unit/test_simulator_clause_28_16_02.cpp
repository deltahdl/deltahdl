#include <gtest/gtest.h>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TriregResolution, TriregRetainsPrevValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();

  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = uint64_t{0};  // z = (aval=0, bval=1)
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(TriregResolution, InCapacitiveStateWhenAllDriversZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 55);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = uint64_t{0};  // z = (aval=0, bval=1)
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  EXPECT_TRUE(net.InCapacitiveState());
}

TEST(TriregResolution, NotInCapacitiveStateWhenDriven) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 7));
  EXPECT_FALSE(net.InCapacitiveState());
}

TEST(TriregResolution, NotInCapacitiveStateForNonTrireg) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = uint64_t{0};  // z = (aval=0, bval=1)
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  EXPECT_FALSE(net.InCapacitiveState());
}

TEST(TriregResolution, MixedZAndDrivenResolvesToDriven) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = uint64_t{0};  // z = (aval=0, bval=1)
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 99));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(TriregResolution, NotInCapacitiveStateWhenAnyDriverNonZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 55);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = uint64_t{0};  // z = (aval=0, bval=1)
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 1));
  EXPECT_FALSE(net.InCapacitiveState());
}

TEST(TriregResolution, RetainsXStateWhenDriversTurnOff) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  var->value.words[0].aval = 0xFF;  // held x = (aval=1, bval=1)
  var->value.words[0].bval = 0xFF;
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = uint64_t{0};  // z = (aval=0, bval=1)
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xFFu);  // retained x
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(TriregResolution, RetainsPrevValueWhenAllOfMultipleDriversTurnOff) {
  // §28.16.2: when the drivers of a trireg transition to off (z), the net keeps
  // the last 1/0/x value it held and z never propagates onto it. Exercise the
  // multi-driver case where every driver has turned off simultaneously.
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 73);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto z_drv_a = MakeLogic4Vec(arena, 8);
  z_drv_a.words[0].aval = uint64_t{0};  // z = (aval=0, bval=1)
  z_drv_a.words[0].bval = ~uint64_t{0};
  auto z_drv_b = MakeLogic4Vec(arena, 8);
  z_drv_b.words[0].aval = uint64_t{0};  // z = (aval=0, bval=1)
  z_drv_b.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv_a);
  net.drivers.push_back(z_drv_b);
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 73u);
  EXPECT_TRUE(net.InCapacitiveState());
}

TEST(TriregResolution, HoldsInitialZStateWhenUndriven) {
  // §28.16.2: a trireg can hold a z logic state when z is the initial logic
  // state of the net. With no drivers present nothing charges the storage
  // node, so the initial z persists.
  Arena arena;
  auto* var = arena.Create<Variable>();
  auto z_val = MakeLogic4Vec(arena, 8);
  z_val.words[0].aval = uint64_t{0};  // z = (aval=0, bval=1)
  z_val.words[0].bval = ~uint64_t{0};
  var->value = z_val;
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  // No drivers added: the trireg is undriven from elaboration onward.
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);  // held z = (aval=0, bval=1)
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(TriregResolution, XDriverResolvesLikeWire) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto x_drv = MakeLogic4Vec(arena, 8);
  x_drv.words[0].aval = 0xFF;  // x = (aval=1, bval=1)
  x_drv.words[0].bval = 0xFF;
  net.drivers.push_back(x_drv);
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xFFu);  // x driver passes through
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

// ---------------------------------------------------------------------------
// End-to-end observations of §28.16.2's own rules, with every input built from
// real source and driven through parse -> elaborate -> lower -> run. The net's
// resolved value/state is read back from the SimContext, so the rule is
// observed exactly as production resolves the trireg during a run rather than
// through a hand-built Net or a hand-set is_forced flag.
// ---------------------------------------------------------------------------

// §28.16.2: a trireg can hold a z logic state when the net is forced to z with
// a force statement (see §10.6.2). Drive the trireg to 1, then force it to z
// from real force syntax; the forced z persists on the net even though a driver
// is present. This is the only path (besides an initial z) by which z reaches a
// trireg, since a released driver would otherwise leave the last 1/0/x held.
TEST(TriregChargeDecayRuntime, ForceHoldsZLogicState) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  trireg cap;\n"
      "  assign cap = en ? 1'b1 : 1'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"  // drive cap to 1
      "    #1;\n"
      "    force cap = 1'bz;\n"  // §10.6.2: force the trireg to z
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* net = f.ctx.FindNet("cap");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  EXPECT_TRUE(net->resolved->is_forced);
  EXPECT_EQ(net->resolved->value.words[0].aval & 1u,
            0u);  // z = (aval=0,bval=1)
  EXPECT_EQ(net->resolved->value.words[0].bval & 1u, 1u);
}

// §28.16.2: the z held above is purely an effect of the force. Releasing the
// force (§10.6.2) returns the trireg to ordinary resolution: with a driver
// still supplying 1, the net follows that driver and no longer holds z --
// confirming z does not otherwise propagate onto a trireg.
TEST(TriregChargeDecayRuntime, ReleasingForceDropsHeldZAndFollowsDriver) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  trireg cap;\n"
      "  assign cap = en ? 1'b1 : 1'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    force cap = 1'bz;\n"
      "    #1;\n"
      "    release cap;\n"  // §10.6.2: drop the forced z
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* net = f.ctx.FindNet("cap");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  EXPECT_FALSE(net->resolved->is_forced);
  EXPECT_FALSE(net->InCapacitiveState());  // driver 1 is active again
  EXPECT_EQ(net->resolved->value.words[0].aval & 1u, 1u);  // follows driver = 1
  EXPECT_EQ(net->resolved->value.words[0].bval & 1u, 0u);
}

}  // namespace
