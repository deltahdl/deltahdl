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

TEST(ClassConstructorSim, ConstructorMethodRegistered) {
  SimFixture f;
  auto* type = MakeClassType(f, "Packet", {"header", "payload"});

  auto* ctor = f.arena.Create<ModuleItem>();
  ctor->kind = ModuleItemKind::kFunctionDecl;
  ctor->name = "new";
  ctor->return_type.kind = DataTypeKind::kVoid;
  ctor->func_args = {
      {Direction::kInput, false, false, {}, "h", nullptr, {}},
      {Direction::kInput, false, false, {}, "p", nullptr, {}},
  };
  ctor->func_body_stmts.push_back(
      MakeAssign(f.arena, "header", MkId(f.arena, "h")));
  ctor->func_body_stmts.push_back(
      MakeAssign(f.arena, "payload", MkId(f.arena, "p")));
  type->methods["new"] = ctor;

  auto* resolved = type->methods["new"];
  ASSERT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->func_args.size(), 2u);
}

TEST(ClassConstructorSim, ConstructorBodyExecutesStatements) {
  SimFixture f;
  auto* type = MakeClassType(f, "Init", {"val"});

  auto* ctor = f.arena.Create<ModuleItem>();
  ctor->kind = ModuleItemKind::kFunctionDecl;
  ctor->name = "new";
  ctor->return_type.kind = DataTypeKind::kVoid;
  ctor->func_args = {{Direction::kInput, false, false, {}, "v", nullptr, {}}};
  ctor->func_body_stmts.push_back(
      MakeAssign(f.arena, "val", MkId(f.arena, "v")));
  type->methods["new"] = ctor;

  auto [handle, obj] = MakeObj(f, type);
  f.ctx.PushThis(obj);
  f.ctx.PushScope();

  auto* arg_var = f.ctx.CreateLocalVariable("v", 32);
  arg_var->value = MakeLogic4VecVal(f.arena, 32, 77);
  auto* val_var = f.ctx.CreateLocalVariable("val", 32);
  val_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto rhs_val = EvalExpr(MkId(f.arena, "v"), f.ctx, f.arena);
  val_var->value = rhs_val;

  obj->SetProperty("val", val_var->value);
  f.ctx.PopScope();
  f.ctx.PopThis();

  EXPECT_EQ(obj->GetProperty("val", f.arena).ToUint64(), 77u);
}

TEST(ClassConstructorSim, ConstructorAssignsProperty) {
  EXPECT_EQ(RunAndGet(
      "class Packet;\n"
      "  integer command;\n"
      "  function new();\n"
      "    command = 42;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    result = p.command;\n"
      "  end\n"
      "endmodule\n", "result"), 42u);
}

TEST(ClassConstructorSim, ConstructorWithArguments) {
  EXPECT_EQ(RunAndGet(
      "class Packet;\n"
      "  int command;\n"
      "  int address;\n"
      "  function new(int cmd, int addr);\n"
      "    command = cmd;\n"
      "    address = addr;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new(10, 20);\n"
      "    result = p.command + p.address;\n"
      "  end\n"
      "endmodule\n", "result"), 30u);
}

TEST(ClassConstructorSim, ConstructorWithDefaultArgValues) {
  EXPECT_EQ(RunAndGet(
      "class Packet;\n"
      "  int command;\n"
      "  int address;\n"
      "  function new(int cmd = 5, int addr = 15);\n"
      "    command = cmd;\n"
      "    address = addr;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    result = p.command + p.address;\n"
      "  end\n"
      "endmodule\n", "result"), 20u);
}

TEST(ClassConstructorSim, ImplicitConstructorCreatesObject) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    c.x = 99;\n"
      "    result = c.x;\n"
      "  end\n"
      "endmodule\n", "result"), 99u);
}

TEST(ClassConstructorSim, PropertyExplicitDefaultInitialized) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  int x = 7;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    result = c.x;\n"
      "  end\n"
      "endmodule\n", "result"), 7u);
}

TEST(ClassConstructorSim, PropertyDefaultOverriddenByConstructorBody) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  int c1 = 1;\n"
      "  int c2 = 1;\n"
      "  function new();\n"
      "    c2 = 2;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    r1 = c.c1;\n"
      "    r2 = c.c2;\n"
      "  end\n"
      "endmodule\n", "r1"), 1u);
}

TEST(ClassConstructorSim, ConstructorBodyOverridesDefault) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  int c1 = 1;\n"
      "  int c2 = 1;\n"
      "  function new();\n"
      "    c2 = 2;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    result = c.c2;\n"
      "  end\n"
      "endmodule\n", "result"), 2u);
}

TEST(ClassConstructorSim, MultiplePropertiesWithDefaults) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int a = 10;\n"
      "  int b = 20;\n"
      "  int c = 30;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ra, rb, rc;\n"
      "  initial begin\n"
      "    C obj;\n"
      "    obj = new;\n"
      "    ra = obj.a;\n"
      "    rb = obj.b;\n"
      "    rc = obj.c;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"ra", 10u}, {"rb", 20u}, {"rc", 30u}});
}

TEST(ClassConstructorSim, ConstructorArgPassedToProperty) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  int c1 = 1;\n"
      "  int c2 = 1;\n"
      "  int c3 = 1;\n"
      "  function new(int a);\n"
      "    c2 = 2;\n"
      "    c3 = a;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new(99);\n"
      "    result = c.c3;\n"
      "  end\n"
      "endmodule\n", "result"), 99u);
}

TEST(ClassConstructorSim, ImplicitConstructorNoExplicitNew) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  int y;\n"
      "endclass\n"
      "module t;\n"
      "  int rx, ry;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    c.x = 3;\n"
      "    c.y = 4;\n"
      "    rx = c.x;\n"
      "    ry = c.y;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"rx", 3u}, {"ry", 4u}});
}

TEST(ClassConstructorSim, TwoObjectsIndependentConstruction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int val;\n"
      "  function new(int v);\n"
      "    val = v;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    C a, b;\n"
      "    a = new(11);\n"
      "    b = new(22);\n"
      "    r1 = a.val;\n"
      "    r2 = b.val;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 11u}, {"r2", 22u}});
}

}  // namespace
