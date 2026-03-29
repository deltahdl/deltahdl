#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(AbstractClassSimulation, AbstractClassFlag) {
  SimFixture f;
  auto* abstract_type = MakeClassType(f, "AbstractBase", {});
  abstract_type->is_abstract = true;

  EXPECT_TRUE(abstract_type->is_abstract);
}

TEST(AbstractClassSimulation, PureVirtualMethodNullBody) {
  SimFixture f;
  auto* abstract_type = MakeClassType(f, "Shape", {});
  abstract_type->is_abstract = true;

  abstract_type->vtable.push_back({"area", nullptr, abstract_type});
  EXPECT_EQ(abstract_type->vtable[0].method, nullptr);

  auto* concrete = MakeClassType(f, "Circle", {"radius"});
  concrete->parent = abstract_type;
  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "area";
  method->func_body_stmts.push_back(MakeReturn(f.arena, MkInt(f.arena, 314)));
  concrete->vtable.push_back({"area", method, concrete});

  auto [handle, obj] = MakeObj(f, concrete);
  auto* resolved = obj->ResolveVirtualMethod("area");
  EXPECT_EQ(resolved, method);
}

TEST(AbstractClassSimulation, MultiplePureVirtualsOverridden) {
  SimFixture f;
  auto* abstract_type = MakeClassType(f, "Base", {});
  abstract_type->is_abstract = true;
  abstract_type->vtable.push_back({"area", nullptr, abstract_type});
  abstract_type->vtable.push_back({"perimeter", nullptr, abstract_type});

  auto* concrete = MakeClassType(f, "Rect", {"w", "h"});
  concrete->parent = abstract_type;

  auto* area_fn = f.arena.Create<ModuleItem>();
  area_fn->kind = ModuleItemKind::kFunctionDecl;
  area_fn->name = "area";
  concrete->vtable.push_back({"area", area_fn, concrete});

  auto* perim_fn = f.arena.Create<ModuleItem>();
  perim_fn->kind = ModuleItemKind::kFunctionDecl;
  perim_fn->name = "perimeter";
  concrete->vtable.push_back({"perimeter", perim_fn, concrete});

  auto [handle, obj] = MakeObj(f, concrete);
  EXPECT_EQ(obj->ResolveVirtualMethod("area"), area_fn);
  EXPECT_EQ(obj->ResolveVirtualMethod("perimeter"), perim_fn);
}

TEST(AbstractClassSimulation, AbstractExtendsAbstractVtable) {
  SimFixture f;
  auto* base = MakeClassType(f, "Shape", {});
  base->is_abstract = true;
  base->vtable.push_back({"area", nullptr, base});

  auto* mid = MakeClassType(f, "Shape2D", {});
  mid->is_abstract = true;
  mid->parent = base;
  mid->vtable.push_back({"area", nullptr, base});
  mid->vtable.push_back({"perimeter", nullptr, mid});

  EXPECT_EQ(mid->vtable[0].method, nullptr);
  EXPECT_EQ(mid->vtable[1].method, nullptr);
}

TEST(AbstractClassSimulation, ConcreteClassNotAbstract) {
  SimFixture f;
  auto* type = MakeClassType(f, "ConcreteClass", {"x"});
  EXPECT_FALSE(type->is_abstract);
}

TEST(AbstractClassSimulation, LoweredAbstractClassIsAbstract) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class Base;\n"
      "  pure virtual function void work();\n"
      "endclass\n"
      "module t; endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  auto* info = f.ctx.FindClassType("Base");
  ASSERT_NE(info, nullptr);
  EXPECT_TRUE(info->is_abstract);
}

TEST(AbstractClassSimulation, LoweredPureVirtualNullInVtable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class Base;\n"
      "  pure virtual function int compute();\n"
      "endclass\n"
      "module t; endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  auto* info = f.ctx.FindClassType("Base");
  ASSERT_NE(info, nullptr);
  ASSERT_FALSE(info->vtable.empty());
  EXPECT_EQ(info->vtable[0].method, nullptr);
}

TEST(AbstractClassSimulation, ConcreteSubclassOfAbstractBaseConstructed) {
  EXPECT_EQ(RunAndGet(
      "virtual class Base;\n"
      "  pure virtual function int compute();\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  virtual function int compute();\n"
      "    compute = 42;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    result = d.compute();\n"
      "  end\n"
      "endmodule\n", "result"), 42u);
}

TEST(AbstractClassSimulation, EmptyBodyVirtualMethodIsCallable) {
  EXPECT_EQ(RunAndGet(
      "class Base;\n"
      "  virtual function int send(bit[31:0] data);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Base b;\n"
      "    b = new;\n"
      "    b.send(0);\n"
      "    result = 1;\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

}  // namespace
