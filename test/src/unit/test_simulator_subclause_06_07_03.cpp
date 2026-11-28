#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <format>
#include <initializer_list>
#include <string>
#include <string_view>
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

TEST(NettypeInitialization, UndrivenTwoStateIntegralNettypeNetsDefaultToZero) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  nettype bit [3:0] b_t;\n"
      "  nettype int i_t;\n"
      "  nettype byte y_t;\n"
      "  nettype shortint s_t;\n"
      "  nettype longint l_t;\n"
      "  typedef struct packed { bit [1:0] a; bit b; } ps_t;\n"
      "  nettype ps_t p_t;\n"
      "  b_t b; i_t i; y_t y; s_t s; l_t l; p_t p;\n"
      "  initial #1 $display(\"%b %0d %0d %0d %0d %b\", b, i, y, s, l, p);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0000 0 0 0 0 000\n");
}

TEST(NettypeInitialization, UndrivenRealAndShortrealNettypeNetsDefaultToZero) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  nettype real r_t;\n"
      "  nettype shortreal s_t;\n"
      "  r_t r; s_t s;\n"
      "  initial #1 $display(\"%f %f\", r, s);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0.000000 0.000000\n");
}

TEST(NettypeInitialization,
     UndrivenFourStatePackedStructNettypeNetsDefaultToX) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef struct packed { logic [1:0] a; logic b; } p4_t;\n"
      "  typedef struct packed { bit [1:0] a; logic b; } pm_t;\n"
      "  nettype p4_t n4_t;\n"
      "  nettype pm_t nm_t;\n"
      "  n4_t p4; nm_t pm;\n"
      "  initial #1 $display(\"%b %b\", p4, pm);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xxx xxx\n");
}

TEST(NettypeInitialization,
     UndrivenUnpackedStructNettypeNetTakesItsMemberInitializers) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef struct { int a = 5; bit [3:0] b = 4'hA; } s_t;\n"
      "  nettype s_t n_t;\n"
      "  n_t n;\n"
      "  initial #1 $display(\"%0d %h\", n.a, n.b);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5 a\n");
}

TEST(NettypeInitialization,
     UndrivenUnpackedStructNettypeNetMembersTakeTheirOwnDefaults) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef struct { int a; logic c; } s_t;\n"
      "  nettype s_t n_t;\n"
      "  n_t n;\n"
      "  initial #1 $display(\"%0d %b\", n.a, n.c);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 x\n");
}

TEST(NettypeInitialization,
     DISABLED_UndrivenUnpackedArrayNettypeNetElementsDefaultToZero) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef bit ab_t [2];\n"
      "  typedef int ai_t [2];\n"
      "  nettype ab_t nb_t;\n"
      "  nettype ai_t ni_t;\n"
      "  nb_t b; ni_t i;\n"
      "  initial #1 $display(\"%b %b %0d %0d\", b[0], b[1], i[0], i[1]);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 0 0 0\n");
}

TEST(NettypeInitialization,
     TwoStateNettypeNetHoldsItsDefaultForAProcedureAtTimeZero) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  nettype bit [3:0] b_t;\n"
      "  nettype int i_t;\n"
      "  b_t b; i_t i;\n"
      "  initial $display(\"%b %0d\", b, i);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0000 0\n");
}

TEST(NettypeInitialization,
     UndrivenResolvedNettypeNetTakesItsFunctionOfNoDrivers) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  function automatic int f(input int d[]);\n"
      "    return 7;\n"
      "  endfunction\n"
      "  function automatic logic [3:0] g(input logic [3:0] d[]);\n"
      "    return 4'b1010;\n"
      "  endfunction\n"
      "  nettype int r_t with f;\n"
      "  nettype logic [3:0] q_t with g;\n"
      "  r_t r; q_t q;\n"
      "  initial #1 $display(\"%0d %b\", r, q);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "7 1010\n");
}

constexpr std::string_view kDefaultNettypes =
    "  typedef struct { int a = 5; bit [3:0] b = 4'hA; logic c; } s_t;\n"
    "  function automatic int rsum(input int d[]);\n"
    "    rsum = 7;\n"
    "    foreach (d[k]) rsum += d[k];\n"
    "  endfunction\n"
    "  nettype bit [3:0] b_t;\n"
    "  nettype int i_t;\n"
    "  nettype s_t n_t;\n"
    "  nettype int r_t with rsum;\n"
    "  nettype logic [3:0] l_t;\n";

constexpr std::string_view kDefaultNets =
    "  b_t b; i_t i; n_t n; r_t r; l_t l;\n"
    "  wire [3:0] w;\n"
    "  initial begin\n"
    "    $display(\"%b %0d\", b, i);\n"
    "    #1 $display(\"%b %0d %0d %h %b %0d %b %b\", b, i, n.a, n.b, n.c, r,\n"
    "        l, w);\n"
    "  end\n";

struct NetPlace {
  std::string_view name;
  std::string_view head;
  std::string_view open;
  std::string_view close;
  std::string_view tail;
};

constexpr std::initializer_list<NetPlace> kNetPlaces = {
    {"module", "module top;\n", "", "", "endmodule\n"},
    {"interface", "interface host;\n", "", "",
     "endinterface\nmodule top;\n  host h();\nendmodule\n"},
    {"program", "program host;\n", "", "",
     "endprogram\nmodule top;\n  host h();\nendmodule\n"},
    {"if generate block", "module top;\n", "  if (1) begin : g\n", "  end\n",
     "endmodule\n"},
    {"loop generate block", "module top;\n",
     "  for (genvar k = 0; k < 1; k++) begin : g\n", "  end\n", "endmodule\n"},
};

TEST(NettypeInitialization,
     UndrivenNettypeNetsTakeTheirDefaultsWhereverDeclared) {
  for (const NetPlace& place : kNetPlaces) {
    SCOPED_TRACE(place.name);
    SimFixture f;
    EXPECT_EQ(RunCapture(std::format("{}{}{}{}{}{}", place.head,
                                     kDefaultNettypes, place.open, kDefaultNets,
                                     place.close, place.tail),
                         f),
              "0000 0\n0000 0 5 a x 7 xxxx zzzz\n");
  }
}
