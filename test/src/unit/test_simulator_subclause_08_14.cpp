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

}  // namespace
