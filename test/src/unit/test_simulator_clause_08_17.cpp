#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ChainedConstructorSimulation, SuperNewChaining) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"base_val"});
  auto* derived = MakeClassType(f, "Derived", {"child_val"});
  derived->parent = base;

  auto [handle, obj] = MakeObj(f, derived);

  obj->SetProperty("base_val", MakeLogic4VecVal(f.arena, 32, 10));

  obj->SetProperty("child_val", MakeLogic4VecVal(f.arena, 32, 20));

  EXPECT_EQ(obj->GetProperty("base_val", f.arena).ToUint64(), 10u);
  EXPECT_EQ(obj->GetProperty("child_val", f.arena).ToUint64(), 20u);
}

TEST(ChainedConstructorSimulation, SuperNewWithArgs) {
  SimFixture f;
  auto* base = MakeClassType(f, "Vehicle", {"speed"});
  auto* ctor = f.arena.Create<ModuleItem>();
  ctor->kind = ModuleItemKind::kFunctionDecl;
  ctor->name = "new";
  ctor->return_type.kind = DataTypeKind::kVoid;
  ctor->func_args = {{Direction::kInput, false, false, {}, "s", nullptr, {}}};
  ctor->func_body_stmts.push_back(
      MakeAssign(f.arena, "speed", MkId(f.arena, "s")));
  base->methods["new"] = ctor;

  auto* derived = MakeClassType(f, "Car", {"doors"});
  derived->parent = base;

  auto it = derived->parent->methods.find("new");
  ASSERT_NE(it, derived->parent->methods.end());
  auto* base_ctor = it->second;
  ASSERT_NE(base_ctor, nullptr);
  EXPECT_EQ(base_ctor->func_args.size(), 1u);
}

TEST(ChainedConstructorSimulation, ThreeLevelConstructorChaining) {
  SimFixture f;
  auto* grand = MakeClassType(f, "Grand", {"g_val"});
  auto* mid = MakeClassType(f, "Mid", {"m_val"});
  mid->parent = grand;
  auto* leaf = MakeClassType(f, "Leaf", {"l_val"});
  leaf->parent = mid;

  auto [handle, obj] = MakeObj(f, leaf);

  obj->SetProperty("g_val", MakeLogic4VecVal(f.arena, 32, 1));
  obj->SetProperty("m_val", MakeLogic4VecVal(f.arena, 32, 2));
  obj->SetProperty("l_val", MakeLogic4VecVal(f.arena, 32, 3));

  EXPECT_EQ(obj->GetProperty("g_val", f.arena).ToUint64(), 1u);
  EXPECT_EQ(obj->GetProperty("m_val", f.arena).ToUint64(), 2u);
  EXPECT_EQ(obj->GetProperty("l_val", f.arena).ToUint64(), 3u);
}

TEST(ChainedConstructorSimulation, BaseConstructorResolvable) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"x"});
  auto* ctor = f.arena.Create<ModuleItem>();
  ctor->kind = ModuleItemKind::kFunctionDecl;
  ctor->name = "new";
  base->methods["new"] = ctor;

  auto* derived = MakeClassType(f, "Child", {"y"});
  derived->parent = base;

  auto [handle, obj] = MakeObj(f, derived);
  auto* resolved = obj->ResolveMethod("new");
  EXPECT_EQ(resolved, ctor);
}

TEST(ChainedConstructorSimulation, SuperNewWithArgsInitializesBase) {
  EXPECT_EQ(RunAndGet(
      "class Base;\n"
      "  int x;\n"
      "  function new(int v); x = v; endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function new(int v); super.new(v); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Derived d = new(42);\n"
      "    result = d.x;\n"
      "  end\n"
      "endmodule\n", "result"), 42u);
}

TEST(ChainedConstructorSimulation, ImplicitSuperNewInitializesBase) {
  EXPECT_EQ(RunAndGet(
      "class Base;\n"
      "  int x;\n"
      "  function new(); x = 7; endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Derived d = new;\n"
      "    result = d.x;\n"
      "  end\n"
      "endmodule\n", "result"), 7u);
}

TEST(ChainedConstructorSimulation, ThreeLevelChainingEndToEnd) {
  EXPECT_EQ(RunAndGet(
      "class A;\n"
      "  int a_val;\n"
      "  function new(); a_val = 1; endfunction\n"
      "endclass\n"
      "class B extends A;\n"
      "  int b_val;\n"
      "  function new(); super.new(); b_val = 2; endfunction\n"
      "endclass\n"
      "class C extends B;\n"
      "  int c_val;\n"
      "  function new(); super.new(); c_val = 3; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    result = c.a_val + c.b_val * 10 + c.c_val * 100;\n"
      "  end\n"
      "endmodule\n", "result"), 321u);
}

TEST(ChainedConstructorSimulation, BaseConstructorRunsBeforeDerived) {
  EXPECT_EQ(RunAndGet(
      "class Base;\n"
      "  int x;\n"
      "  function new(); x = 10; endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int y;\n"
      "  function new();\n"
      "    super.new();\n"
      "    y = x + 5;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Derived d = new;\n"
      "    result = d.y;\n"
      "  end\n"
      "endmodule\n", "result"), 15u);
}

TEST(ChainedConstructorSimulation, ImplicitSuperNewWithDerivedConstructor) {
  EXPECT_EQ(RunAndGet(
      "class Base;\n"
      "  int x;\n"
      "  function new(); x = 100; endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int y;\n"
      "  function new(); y = 200; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Derived d = new;\n"
      "    result = d.x + d.y;\n"
      "  end\n"
      "endmodule\n", "result"), 300u);
}

TEST(ChainedConstructorSimulation, PropertyDefaultsInitializedDuringChaining) {
  EXPECT_EQ(RunAndGet(
      "class Base;\n"
      "  int x = 50;\n"
      "  function new(); endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int y = 25;\n"
      "  function new(); super.new(); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Derived d = new;\n"
      "    result = d.x + d.y;\n"
      "  end\n"
      "endmodule\n", "result"), 75u);
}

}  // namespace
