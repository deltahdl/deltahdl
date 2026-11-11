#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "parser/ast_module.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(OverriddenMemberSimulation, SubclassIsValidBaseObject) {
  SimFixture f;
  auto* packet = MakeClassType(f, "Packet", {"i"});
  auto* linked = MakeClassType(f, "LinkedPacket", {"i"});
  linked->parent = packet;

  EXPECT_TRUE(linked->IsA(packet));
  EXPECT_FALSE(packet->IsA(linked));
}

TEST(OverriddenMemberSimulation, MultiLevelSubclassIsValidBaseObject) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"x"});
  auto* mid = MakeClassType(f, "Mid", {"x"});
  mid->parent = base;
  auto* leaf = MakeClassType(f, "Leaf", {"x"});
  leaf->parent = mid;

  EXPECT_TRUE(leaf->IsA(base));
  EXPECT_TRUE(leaf->IsA(mid));
  EXPECT_FALSE(base->IsA(leaf));
}

TEST(OverriddenMemberSimulation, VirtualMethodDispatchesThroughVtable) {
  SimFixture f;
  auto* base = MakeClassType(f, "Packet", {});
  auto* derived = MakeClassType(f, "LinkedPacket", {});
  derived->parent = base;

  auto* base_get = f.arena.Create<ModuleItem>();
  base_get->kind = ModuleItemKind::kFunctionDecl;
  base_get->name = "get";
  auto* derived_get = f.arena.Create<ModuleItem>();
  derived_get->kind = ModuleItemKind::kFunctionDecl;
  derived_get->name = "get";

  base->vtable.push_back({"get", base_get, base});
  derived->vtable.push_back({"get", derived_get, derived});

  auto [handle, obj] = MakeObj(f, derived);
  EXPECT_EQ(obj->ResolveVirtualMethod("get"), derived_get);
  EXPECT_EQ(obj->ResolveMethod("get"), nullptr);
}

TEST(OverriddenMemberSimulation, E2eSubclassHandleAssignedToBaseVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Packet;\n"
      "  integer i;\n"
      "endclass\n"
      "class LinkedPacket extends Packet;\n"
      "  integer i;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    LinkedPacket lp;\n"
      "    Packet p;\n"
      "    lp = new;\n"
      "    p = lp;\n"
      "    result = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 1u}});
}

TEST(OverriddenMemberSimulation, E2eBasePropertyAccessThroughBaseHandle) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  integer i = 1;\n"
                      "endclass\n"
                      "class LinkedPacket extends Packet;\n"
                      "  integer i = 2;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    LinkedPacket lp;\n"
                      "    Packet p;\n"
                      "    lp = new;\n"
                      "    p = lp;\n"
                      "    result = p.i;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(OverriddenMemberSimulation, E2eBaseMethodAccessThroughBaseHandle) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  function integer get();\n"
                      "    get = 10;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class LinkedPacket extends Packet;\n"
                      "  function integer get();\n"
                      "    get = 20;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    LinkedPacket lp;\n"
                      "    Packet p;\n"
                      "    lp = new;\n"
                      "    p = lp;\n"
                      "    result = p.get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            10u);
}

TEST(OverriddenMemberSimulation, E2eDerivedAccessSeesOverriddenMembers) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Packet;\n"
      "  integer i = 1;\n"
      "  function integer get();\n"
      "    get = 10;\n"
      "  endfunction\n"
      "endclass\n"
      "class LinkedPacket extends Packet;\n"
      "  integer i = 2;\n"
      "  function integer get();\n"
      "    get = 20;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ri, rget;\n"
      "  initial begin\n"
      "    LinkedPacket lp;\n"
      "    lp = new;\n"
      "    ri = lp.i;\n"
      "    rget = lp.get();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"ri", 2u}, {"rget", 20u}});
}

TEST(OverriddenMemberSimulation, E2eBaseAndDerivedAccessContrast) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Packet;\n"
      "  integer i = 1;\n"
      "endclass\n"
      "class LinkedPacket extends Packet;\n"
      "  integer i = 2;\n"
      "endclass\n"
      "module t;\n"
      "  int r_base, r_derived;\n"
      "  initial begin\n"
      "    LinkedPacket lp;\n"
      "    Packet p;\n"
      "    lp = new;\n"
      "    p = lp;\n"
      "    r_base = p.i;\n"
      "    r_derived = lp.i;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r_base", 1u}, {"r_derived", 2u}});
}

TEST(OverriddenMemberSimulation, E2eNonOverriddenMemberAccessibleThroughBase) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  integer x = 5;\n"
                      "endclass\n"
                      "class LinkedPacket extends Packet;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    LinkedPacket lp;\n"
                      "    Packet p;\n"
                      "    lp = new;\n"
                      "    p = lp;\n"
                      "    result = p.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            5u);
}

TEST(OverriddenMemberSimulation, WriteThroughBaseTypeTargetsBaseSlot) {
  SimFixture f;
  auto* base = MakeClassType(f, "Packet", {"i"});
  auto* derived = MakeClassType(f, "LinkedPacket", {"i"});
  derived->parent = base;

  auto [handle, obj] = MakeObj(f, derived);
  obj->properties["Packet::i"] = MakeLogic4VecVal(f.arena, 32, 1);
  obj->properties["LinkedPacket::i"] = MakeLogic4VecVal(f.arena, 32, 2);

  obj->SetPropertyForType("i", base, MakeLogic4VecVal(f.arena, 32, 7));
  EXPECT_EQ(obj->GetPropertyForType("i", base, f.arena).ToUint64(), 7u);
  EXPECT_EQ(obj->GetPropertyForType("i", derived, f.arena).ToUint64(), 2u);
}

TEST(OverriddenMemberSimulation,
     E2eBaseMethodReadsBasePropertyThroughBaseHandle) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  integer i = 1;\n"
                      "  function integer get();\n"
                      "    get = i;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class LinkedPacket extends Packet;\n"
                      "  integer i = 2;\n"
                      "  function integer get();\n"
                      "    get = -i;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    LinkedPacket lp;\n"
                      "    Packet p;\n"
                      "    lp = new;\n"
                      "    p = lp;\n"
                      "    result = p.get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(OverriddenMemberSimulation, E2eIntermediateHandleSeesIntermediateMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class A;\n"
      "  integer x = 1;\n"
      "endclass\n"
      "class B extends A;\n"
      "  integer x = 2;\n"
      "endclass\n"
      "class C extends B;\n"
      "  integer x = 3;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c;\n"
      "    B b;\n"
      "    c = new;\n"
      "    b = c;\n"
      "    result = b.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 2u}});
}

TEST(OverriddenMemberSimulation, E2eBasePropertyThroughBaseTypedArgument) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  integer i = 1;\n"
                      "endclass\n"
                      "class LinkedPacket extends Packet;\n"
                      "  integer i = 2;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  function integer read_i(Packet p);\n"
                      "    read_i = p.i;\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    LinkedPacket lp;\n"
                      "    lp = new;\n"
                      "    result = read_i(lp);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(OverriddenMemberSimulation, E2eBaseMethodThroughBaseTypedArgument) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  function integer get();\n"
                      "    get = 10;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class LinkedPacket extends Packet;\n"
                      "  function integer get();\n"
                      "    get = 20;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  function integer call_get(Packet p);\n"
                      "    call_get = p.get();\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    LinkedPacket lp;\n"
                      "    lp = new;\n"
                      "    result = call_get(lp);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            10u);
}

TEST(OverriddenMemberSimulation, ABaseHandleReachesTheBaseMemberOfEveryKind) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class P;\n"
      "  integer i = 1;\n"
      "  logic [3:0] w = 4'hF;\n"
      "  function integer get(); return i; endfunction\n"
      "  function integer twice(); return get() * 2; endfunction\n"
      "  task tk(output int o); o = 100; endtask\n"
      "  static function int sf(); return 40; endfunction\n"
      "endclass\n"
      "class L extends P;\n"
      "  integer i = 2;\n"
      "  logic [15:0] w = 16'hABCD;\n"
      "  function integer get(); return -i; endfunction\n"
      "  task tk(output int o); o = 200; endtask\n"
      "  static function int sf(); return 41; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2, r3, r4, r5, r6, r7, r8, r9, r10;\n"
      "  initial begin\n"
      "    automatic L lp = new;\n"
      "    automatic P p = lp;\n"
      "    automatic P q[$];\n"
      "    r1 = p.i; r2 = p.get(); r3 = p.w; r4 = p.sf();\n"
      "    p.tk(r5);\n"
      "    r6 = lp.twice();\n"
      "    p.i = 9; r7 = lp.i; r8 = p.i;\n"
      "    q.push_back(lp); r9 = q[0].get();\n"
      "    r10 = lp.w + lp.get() + lp.sf();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 1u},
                    {"r2", 1u},
                    {"r3", 15u},
                    {"r4", 40u},
                    {"r5", 100u},
                    {"r6", 2u},
                    {"r7", 2u},
                    {"r8", 9u},
                    {"r9", 9u},
                    {"r10", 44020u}});
}

TEST(OverriddenMemberSimulation, ABaseHandleReachesTheBaseMemberInEveryPlace) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pk;\n"
      "  class P; int i = 1; function int get(); return i + 10; "
      "endfunction endclass\n"
      "  class L extends P; int i = 2; function int get(); return i + 20; "
      "endfunction endclass\n"
      "endpackage\n"
      "interface itf;\n"
      "  class IP; int i = 3; endclass\n"
      "  class IL extends IP; int i = 4; endclass\n"
      "  function automatic int t(); IL l = new; IP p = l; return p.i; "
      "endfunction\n"
      "endinterface\n"
      "module t;\n"
      "  int r1, r2, r3, r4, r5;\n"
      "  itf i();\n"
      "  class MP; int i = 7; endclass\n"
      "  class ML extends MP; int i = 8; endclass\n"
      "  if (1) begin : g\n"
      "    class GP; int i = 9; endclass\n"
      "    class GL extends GP; int i = 10; endclass\n"
      "    function automatic int t(); GL l = new; GP p = l; return p.i; "
      "endfunction\n"
      "  end\n"
      "  initial begin\n"
      "    automatic pk::L l = new;\n"
      "    automatic pk::P p = l;\n"
      "    automatic ML ml = new;\n"
      "    automatic MP mp = ml;\n"
      "    r1 = p.i + p.get(); r2 = i.t(); r3 = mp.i; r4 = g.t();\n"
      "    r5 = l.get();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"r1", 12u}, {"r2", 3u}, {"r3", 7u}, {"r4", 9u}, {"r5", 22u}});
}

TEST(OverriddenMemberSimulation,
     DISABLED_ABaseHandleReachedThroughAnyExpressionReachesTheBaseMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class P;\n"
      "  integer i = 1;\n"
      "  logic [3:0] w = 4'hF;\n"
      "  static int s = 30;\n"
      "  function integer get(); return i; endfunction\n"
      "endclass\n"
      "class L extends P;\n"
      "  integer i = 2;\n"
      "  logic [15:0] w = 16'hABCD;\n"
      "  static int s = 31;\n"
      "  function integer get(); return -i; endfunction\n"
      "endclass\n"
      "class Holder; P h; endclass\n"
      "class Out;\n"
      "  class NP; int i = 5; endclass\n"
      "  class NL extends NP; int i = 6; endclass\n"
      "  static function int t(); NL l = new; NP p = l; return p.i; "
      "endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2, r3, r4, r5;\n"
      "  function automatic P mk(); L l = new; return l; endfunction\n"
      "  initial begin\n"
      "    automatic L lp = new;\n"
      "    automatic P p = lp;\n"
      "    automatic P arr[2];\n"
      "    automatic Holder ho = new;\n"
      "    r1 = p.s;\n"
      "    r2 = mk().get();\n"
      "    arr[1] = lp; r3 = arr[1].i;\n"
      "    ho.h = lp; r4 = ho.h.w;\n"
      "    r5 = Out::t();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"r1", 30u}, {"r2", 1u}, {"r3", 1u}, {"r4", 15u}, {"r5", 5u}});
}

}  // namespace
