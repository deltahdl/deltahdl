#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "helpers_switch_network.h"
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

// §6.7.3: the resolution function is activated at time zero at least once.
TEST(NettypeInitialization, ResolutionActivatedAtTimeZero) {
  Arena arena;
  Net net = MakeNettypeNet(MakeVar(arena, 1));

  bool activated = false;
  UserNettype nt;
  nt.resolution = [&](Arena& a, const std::vector<Logic4Vec>&) -> Logic4Vec {
    activated = true;
    return MakeLogic4Vec(a, 1);
  };

  InitializeUserDefinedNet(net, nt, arena);
  EXPECT_TRUE(activated);
}

// §6.7.3: the guaranteed time-zero call happens even with no drivers, in which
// case the resolution function is handed an empty driver array.
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

// §6.7.3 + Table 6-7: the default value of a logic (4-state) nettype net is x.
TEST(NettypeInitialization, DefaultIsDataTypeDefault) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net = MakeNettypeNet(var);

  UserNettype nt;
  nt.data_kind = NettypeDataKind::k4StateIntegral;
  InitializeUserDefinedNet(net, nt, arena);

  EXPECT_EQ(ValOf(*var), kValX);
}

// §6.7.3: the data-type default applies across every bit of a multi-bit net.
TEST(NettypeInitialization, MultiBitDefaultIsAllX) {
  Arena arena;
  auto* var = MakeVar(arena, 8);
  Net net = MakeNettypeNet(var);

  UserNettype nt;
  nt.data_kind = NettypeDataKind::k4StateIntegral;
  InitializeUserDefinedNet(net, nt, arena);

  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0x00u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

// §6.7.3: a 2-state data type defaults to zero, not x.
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

// §6.7.3: the initial value is set before the resolution call runs, so the
// resolution function observes the data-type default.
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

// §6.7.3 NOTE: a resolved nettype's value is determined by the resolution
// function executed with an empty array of driver values.
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

// §6.7.3 NOTE: an unresolved logic nettype bit with no drivers is x, not z.
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

// §6.7.3: the resolution result overrides the data-type default.
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

// §6.7.3: a net with no resolved storage cannot be initialized.
TEST(NettypeInitialization, NoResolvedStorageFails) {
  Arena arena;
  Net net;
  net.is_user_nettype = true;

  UserNettype nt;
  EXPECT_FALSE(InitializeUserDefinedNet(net, nt, arena));
}

// §6.7.3: for a struct-typed nettype, initialization expressions for the
// members within the struct are applied; members with no initializer keep the
// data-type default (x).
TEST(NettypeInitialization, StructMemberInitializersApplied) {
  Arena arena;

  std::vector<StructMemberInit> members(2);
  // Low 4 bits: a member initialized to 0b1010.
  members[0].offset = 0;
  members[0].width = 4;
  members[0].has_initializer = true;
  members[0].init_value = MakeLogic4VecVal(arena, 4, 0xA);
  // High 4 bits: a member with no initializer, expected to stay x.
  members[1].offset = 4;
  members[1].width = 4;
  members[1].has_initializer = false;

  Logic4Vec v = InitialStructNetValue(arena, 8, members);

  // Initialized member: known value 0b1010.
  EXPECT_EQ(v.words[0].aval & 0xF, 0xAu);
  EXPECT_EQ(v.words[0].bval & 0xF, 0x0u);
  // Uninitialized member: all x (aval 0, bval 1) across its bits.
  EXPECT_EQ((v.words[0].aval >> 4) & 0xF, 0x0u);
  EXPECT_EQ((v.words[0].bval >> 4) & 0xF, 0xFu);
}

// §6.7.3: the guaranteed time-zero call also occurs when a net has drivers
// whose values do not change at time zero; the resolution function still runs
// and is handed the present driver set.
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

// §6.7.3 + Table 6-7: a real data type defaults to a zero value, not x.
TEST(NettypeInitialization, RealDataTypeDefaultIsZero) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net = MakeNettypeNet(var);

  UserNettype nt;
  nt.data_kind = NettypeDataKind::kReal;
  InitializeUserDefinedNet(net, nt, arena);

  EXPECT_EQ(ValOf(*var), kVal0);
}

// §6.7.3: a struct member initializer is applied at the member's own bit
// offset; a lower member with no initializer is left at the default (x).
TEST(NettypeInitialization, StructMemberInitAtNonZeroOffset) {
  Arena arena;

  std::vector<StructMemberInit> members(2);
  // Low 4 bits: no initializer, expected to stay x.
  members[0].offset = 0;
  members[0].width = 4;
  members[0].has_initializer = false;
  // High 4 bits: a member initialized to 0b0101 at offset 4.
  members[1].offset = 4;
  members[1].width = 4;
  members[1].has_initializer = true;
  members[1].init_value = MakeLogic4VecVal(arena, 4, 0x5);

  Logic4Vec v = InitialStructNetValue(arena, 8, members);

  // Lower member untouched: all x.
  EXPECT_EQ(v.words[0].aval & 0xF, 0x0u);
  EXPECT_EQ(v.words[0].bval & 0xF, 0xFu);
  // Upper member: known value 0b0101 placed at offset 4.
  EXPECT_EQ((v.words[0].aval >> 4) & 0xF, 0x5u);
  EXPECT_EQ((v.words[0].bval >> 4) & 0xF, 0x0u);
}

// §6.7.3: when every struct member carries an initializer, the whole value is
// known and no bits are left at the default x.
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
