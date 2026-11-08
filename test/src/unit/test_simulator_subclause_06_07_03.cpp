#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_switch_network.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

static Variable* MakeVar(Arena& arena, uint32_t width) {
  auto* v = arena.Create<Variable>();
  v->value = MakeLogic4Vec(arena, width);
  return v;
}

static Net MakeNettypeNet(Variable* var) {
  Net net;
  net.type = NetType::kWire;
  net.is_user_nettype = true;
  net.resolved = var;
  return net;
}

TEST(NettypeInitialization, ResolutionAtTimeZeroEvenNoDrivers) {
  Arena arena;
  Net net = MakeNettypeNet(MakeVar(arena, 1));

  bool activated = false;
  UserNettype nt;
  nt.resolution = [&](Arena& a,
                      const std::vector<Logic4Vec>& drivers) -> Logic4Vec {
    activated = true;
    EXPECT_TRUE(drivers.empty());
    return MakeLogic4Vec(a, 1);
  };

  InitializeUserDefinedNet(net, nt, arena);
  EXPECT_TRUE(activated);
}

TEST(NettypeInitialization, MultiBitDefaultIsAllX) {
  Arena arena;
  auto* var = MakeVar(arena, 8);
  Net net = MakeNettypeNet(var);

  UserNettype nt;
  nt.data_kind = NettypeDataKind::k4StateIntegral;
  InitializeUserDefinedNet(net, nt, arena);

  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xFFu);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(NettypeInitialization, TwoStateDefaultIsZero) {
  Arena arena;
  auto* var = MakeVar(arena, 4);
  Net net = MakeNettypeNet(var);

  UserNettype nt;
  nt.data_kind = NettypeDataKind::k2StateIntegral;
  InitializeUserDefinedNet(net, nt, arena);

  EXPECT_EQ(ValOf(*var), kVal0);
  EXPECT_EQ(var->value.words[0].aval & 0xF, 0x0u);
  EXPECT_EQ(var->value.words[0].bval & 0xF, 0x0u);
}

TEST(NettypeInitialization, InitialValueSetBeforeResolution) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net = MakeNettypeNet(var);

  uint8_t value_seen_by_resolution = 0xFF;
  UserNettype nt;
  nt.data_kind = NettypeDataKind::k4StateIntegral;
  nt.resolution = [&](Arena& a, const std::vector<Logic4Vec>&) -> Logic4Vec {
    value_seen_by_resolution = ValOf(*var);
    return MakeLogic4Vec(a, 1);
  };

  InitializeUserDefinedNet(net, nt, arena);

  EXPECT_EQ(value_seen_by_resolution, kValX);
}

TEST(NettypeInitialization, ResolutionWithEmptyDriversSetsResolvedValue) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net = MakeNettypeNet(var);

  UserNettype nt;
  nt.resolution = [](Arena& a,
                     const std::vector<Logic4Vec>& drivers) -> Logic4Vec {
    EXPECT_TRUE(drivers.empty());
    return MakeLogic4VecVal(a, 1, 0);
  };

  InitializeUserDefinedNet(net, nt, arena);
  EXPECT_EQ(ValOf(*var), kVal0);
}

TEST(NettypeInitialization, DefaultIsXNotZ) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net = MakeNettypeNet(var);

  UserNettype nt;
  nt.data_kind = NettypeDataKind::k4StateIntegral;
  InitializeUserDefinedNet(net, nt, arena);

  EXPECT_NE(ValOf(*var), kValZ);
  EXPECT_EQ(ValOf(*var), kValX);
}

TEST(NettypeInitialization, ResolutionOverwritesDefault) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net = MakeNettypeNet(var);

  UserNettype nt;
  nt.data_kind = NettypeDataKind::k4StateIntegral;
  nt.resolution = [](Arena& a, const std::vector<Logic4Vec>&) -> Logic4Vec {
    return MakeLogic4VecVal(a, 1, 1);
  };

  InitializeUserDefinedNet(net, nt, arena);
  EXPECT_EQ(ValOf(*var), kVal1);
}

TEST(NettypeInitialization, NoResolvedStorageFails) {
  Arena arena;
  Net net;
  net.is_user_nettype = true;

  UserNettype nt;
  EXPECT_FALSE(InitializeUserDefinedNet(net, nt, arena));
}

TEST(NettypeInitialization, StructMemberInitializersApplied) {
  Arena arena;

  std::vector<StructMemberInit> members(2);
  members[0].offset = 0;
  members[0].width = 4;
  members[0].has_initializer = true;
  members[0].init_value = MakeLogic4VecVal(arena, 4, 0xA);
  members[1].offset = 4;
  members[1].width = 4;
  members[1].has_initializer = false;

  Logic4Vec v = InitialStructNetValue(arena, 8, members);

  EXPECT_EQ(v.words[0].aval & 0xF, 0xAu);
  EXPECT_EQ(v.words[0].bval & 0xF, 0x0u);
  EXPECT_EQ((v.words[0].aval >> 4) & 0xF, 0xFu);
  EXPECT_EQ((v.words[0].bval >> 4) & 0xF, 0xFu);
}

TEST(NettypeInitialization, ResolutionAtTimeZeroWithDriverPresent) {
  Arena arena;
  Net net = MakeNettypeNet(MakeVar(arena, 1));
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));

  bool activated = false;
  size_t drivers_seen = 0;
  UserNettype nt;
  nt.resolution = [&](Arena& a,
                      const std::vector<Logic4Vec>& drivers) -> Logic4Vec {
    activated = true;
    drivers_seen = drivers.size();
    return drivers.empty() ? MakeLogic4Vec(a, 1) : drivers[0];
  };

  InitializeUserDefinedNet(net, nt, arena);
  EXPECT_TRUE(activated);
  EXPECT_EQ(drivers_seen, 1u);
  EXPECT_EQ(ValOf(*net.resolved), kVal1);
}

TEST(NettypeInitialization, RealDataTypeDefaultIsZero) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net = MakeNettypeNet(var);

  UserNettype nt;
  nt.data_kind = NettypeDataKind::kReal;
  InitializeUserDefinedNet(net, nt, arena);

  EXPECT_EQ(ValOf(*var), kVal0);
}

TEST(NettypeInitialization, StructMemberInitAtNonZeroOffset) {
  Arena arena;

  std::vector<StructMemberInit> members(2);
  members[0].offset = 0;
  members[0].width = 4;
  members[0].has_initializer = false;
  members[1].offset = 4;
  members[1].width = 4;
  members[1].has_initializer = true;
  members[1].init_value = MakeLogic4VecVal(arena, 4, 0x5);

  Logic4Vec v = InitialStructNetValue(arena, 8, members);

  EXPECT_EQ(v.words[0].aval & 0xF, 0xFu);
  EXPECT_EQ(v.words[0].bval & 0xF, 0xFu);
  EXPECT_EQ((v.words[0].aval >> 4) & 0xF, 0x5u);
  EXPECT_EQ((v.words[0].bval >> 4) & 0xF, 0x0u);
}

TEST(NettypeInitialization, AllStructMembersInitialized) {
  Arena arena;

  std::vector<StructMemberInit> members(2);
  members[0].offset = 0;
  members[0].width = 4;
  members[0].has_initializer = true;
  members[0].init_value = MakeLogic4VecVal(arena, 4, 0x3);
  members[1].offset = 4;
  members[1].width = 4;
  members[1].has_initializer = true;
  members[1].init_value = MakeLogic4VecVal(arena, 4, 0xC);

  Logic4Vec v = InitialStructNetValue(arena, 8, members);

  EXPECT_EQ(v.words[0].aval & 0xFF, 0xC3u);
  EXPECT_EQ(v.words[0].bval & 0xFF, 0x00u);
}

TEST(NettypeInitialization, UndrivenLogicNettypeNetDefaultsToXNotZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic nt;\n"
      "  nt n;\n"
      "  wire ord;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* nettype_net = f.ctx.FindNet("n");
  auto* ordinary_net = f.ctx.FindNet("ord");
  ASSERT_NE(nettype_net, nullptr);
  ASSERT_NE(ordinary_net, nullptr);
  ASSERT_TRUE(nettype_net->is_user_nettype);

  EXPECT_EQ(ValOf(*nettype_net->resolved), kValX);
  EXPECT_EQ(ValOf(*ordinary_net->resolved), kValZ);
}

TEST(NettypeInitialization, UndrivenMultiBitLogicNettypeNetDefaultsToAllX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic [7:0] nt;\n"
      "  nt n;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* net = f.ctx.FindNet("n");
  ASSERT_NE(net, nullptr);
  ASSERT_TRUE(net->is_user_nettype);

  EXPECT_EQ(net->resolved->value.words[0].aval & 0xFF, 0xFFu);
  EXPECT_EQ(net->resolved->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(NettypeInitialization, InitialValueVisibleToProcedureAtTimeZero) {
  SimFixture f;
  auto* res = RunAndFindVar(
      "module t;\n"
      "  nettype logic nt;\n"
      "  nt n;\n"
      "  logic [1:0] res;\n"
      "  initial res = {n === 1'bx, n === 1'bz};\n"
      "endmodule\n",
      f, "res");
  ASSERT_NE(res, nullptr);
  EXPECT_EQ(res->value.words[0].aval & 0x3, 0x2u);
  EXPECT_EQ(res->value.words[0].bval & 0x3, 0x0u);
}
