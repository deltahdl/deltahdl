#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// Unit tests: ClassObject / ClassTypeInfo API
// ---------------------------------------------------------------------------

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

TEST(OverriddenMemberSimulation, NonVirtualResolutionFromBaseType) {
  SimFixture f;
  auto* base = MakeClassType(f, "Packet", {});
  auto* base_get = f.arena.Create<ModuleItem>();
  base_get->kind = ModuleItemKind::kFunctionDecl;
  base_get->name = "get";
  base->methods["get"] = base_get;

  auto* derived = MakeClassType(f, "LinkedPacket", {});
  derived->parent = base;
  auto* derived_get = f.arena.Create<ModuleItem>();
  derived_get->kind = ModuleItemKind::kFunctionDecl;
  derived_get->name = "get";
  derived->methods["get"] = derived_get;

  auto [h1, obj1] = MakeObj(f, derived);
  EXPECT_EQ(obj1->ResolveMethod("get"), derived_get);

  auto it = base->methods.find("get");
  ASSERT_NE(it, base->methods.end());
  EXPECT_EQ(it->second, base_get);
}

TEST(OverriddenMemberSimulation, OverriddenPropertyInDerived) {
  SimFixture f;
  auto* base = MakeClassType(f, "Packet", {"i"});
  auto* derived = MakeClassType(f, "LinkedPacket", {"i"});
  derived->parent = base;

  auto [handle, obj] = MakeObj(f, derived);
  obj->SetProperty("i", MakeLogic4VecVal(f.arena, 32, 2));

  EXPECT_EQ(obj->GetProperty("i", f.arena).ToUint64(), 2u);
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

// ---------------------------------------------------------------------------
// End-to-end tests: full pipeline (parse -> elaborate -> lower -> run)
// ---------------------------------------------------------------------------

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
  EXPECT_EQ(RunAndGet(
      "class Packet;\n"
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
      "endmodule\n", "result"), 1u);
}

TEST(OverriddenMemberSimulation, E2eBaseMethodAccessThroughBaseHandle) {
  EXPECT_EQ(RunAndGet(
      "class Packet;\n"
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
      "endmodule\n", "result"), 10u);
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
  EXPECT_EQ(RunAndGet(
      "class Packet;\n"
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
      "endmodule\n", "result"), 5u);
}

}  // namespace
