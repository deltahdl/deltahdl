#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

static Expr* MkBin(Arena& a, TokenKind op, Expr* l, Expr* r) {
  auto* e = a.Create<Expr>();
  e->kind = ExprKind::kBinary;
  e->op = op;
  e->lhs = l;
  e->rhs = r;
  return e;
}

namespace {

TEST(ClassSim, SimpleMethodCall) {
  SimFixture f;
  auto* type = MakeClassType(f, "Counter", {"count"});

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "get_count";
  method->func_body_stmts.push_back(
      MakeReturn(f.arena, MkId(f.arena, "count")));
  type->methods["get_count"] = method;

  auto [handle, obj] = MakeObj(f, type);
  obj->SetProperty("count", MakeLogic4VecVal(f.arena, 32, 99));

  auto* resolved = obj->ResolveMethod("get_count");
  EXPECT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->name, "get_count");
}

TEST(ClassSim, MethodWithArgs) {
  SimFixture f;
  auto* type = MakeClassType(f, "Adder", {"total"});

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "add";
  method->return_type.kind = DataTypeKind::kVoid;
  method->func_args = {{Direction::kInput, false, false, false, {}, "v", nullptr, {}}};
  auto* rhs = MkBin(f.arena, TokenKind::kPlus, MkId(f.arena, "total"),
                    MkId(f.arena, "v"));
  method->func_body_stmts.push_back(MakeAssign(f.arena, "total", rhs));
  type->methods["add"] = method;

  auto [handle, obj] = MakeObj(f, type);
  auto* resolved = obj->ResolveMethod("add");
  EXPECT_NE(resolved, nullptr);
}

TEST(ClassSim, MethodNotFound) {
  SimFixture f;
  auto* type = MakeClassType(f, "Simple", {});
  auto [handle, obj] = MakeObj(f, type);

  auto* resolved = obj->ResolveMethod("nonexistent");
  EXPECT_EQ(resolved, nullptr);
}

TEST(ClassSim, MethodCallReturnValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Counter;\n"
      "  int count;\n"
      "  function new();\n"
      "    count = 42;\n"
      "  endfunction\n"
      "  function int get_count();\n"
      "    return count;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Counter c;\n"
      "    c = new;\n"
      "    result = c.get_count();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 42u}});
}

TEST(ClassSim, MethodCallModifiesProperty) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Acc;\n"
      "  int total;\n"
      "  function new();\n"
      "    total = 0;\n"
      "  endfunction\n"
      "  function void add(int v);\n"
      "    total = total + v;\n"
      "  endfunction\n"
      "  function int get();\n"
      "    return total;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Acc a;\n"
      "    a = new;\n"
      "    a.add(10);\n"
      "    a.add(7);\n"
      "    result = a.get();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 17u}});
}

TEST(ClassSim, MultipleMethodsSameObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Pair;\n"
      "  int x;\n"
      "  int y;\n"
      "  function new();\n"
      "    x = 3;\n"
      "    y = 4;\n"
      "  endfunction\n"
      "  function int get_x();\n"
      "    return x;\n"
      "  endfunction\n"
      "  function int get_y();\n"
      "    return y;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int rx, ry;\n"
      "  initial begin\n"
      "    Pair p;\n"
      "    p = new;\n"
      "    rx = p.get_x();\n"
      "    ry = p.get_y();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"rx", 3u}, {"ry", 4u}});
}

}  // namespace
