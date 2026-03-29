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

TEST(StaticMethodSimulation, StaticMethodResolution) {
  SimFixture f;
  auto* type = MakeClassType(f, "Util", {});

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "helper";
  method->is_static = true;
  method->func_body_stmts.push_back(MakeReturn(f.arena, MkInt(f.arena, 100)));
  type->methods["helper"] = method;

  auto it = type->methods.find("helper");
  ASSERT_NE(it, type->methods.end());
  EXPECT_TRUE(it->second->is_static);
}

TEST(StaticMethodSimulation, StaticMethodCallableWithoutInstance) {
  SimFixture f;
  auto* type = MakeClassType(f, "Counter", {});
  type->properties.push_back({"count", 32, true});
  type->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 0);

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "get_count";
  method->is_static = true;
  method->func_body_stmts.push_back(MakeReturn(f.arena, MkInt(f.arena, 0)));
  type->methods["get_count"] = method;

  auto it = type->methods.find("get_count");
  ASSERT_NE(it, type->methods.end());
  EXPECT_TRUE(it->second->is_static);
}

TEST(StaticMethodSimulation, StaticMethodAccessesStaticProperty) {
  SimFixture f;
  auto* type = MakeClassType(f, "id", {});
  type->properties.push_back({"current", 32, true});
  type->static_properties["current"] = MakeLogic4VecVal(f.arena, 32, 42);

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "next_id";
  method->is_static = true;
  type->methods["next_id"] = method;

  ASSERT_NE(type->methods.count("next_id"), 0u);
  EXPECT_EQ(type->static_properties["current"].ToUint64(), 42u);
}

TEST(StaticMethodSimulation, ClassScopeCallReturnsValue) {
  EXPECT_EQ(RunAndGet(
      "class Util;\n"
      "  static function int answer();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = Util::answer();\n"
      "  end\n"
      "endmodule\n", "result"), 42u);
}

TEST(StaticMethodSimulation, StaticMethodModifiesStaticProperty) {
  EXPECT_EQ(RunAndGet(
      "class Counter;\n"
      "  static int count;\n"
      "  static function void inc();\n"
      "    count = count + 1;\n"
      "  endfunction\n"
      "  static function int get();\n"
      "    return count;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Counter::inc();\n"
      "    Counter::inc();\n"
      "    Counter::inc();\n"
      "    result = Counter::get();\n"
      "  end\n"
      "endmodule\n", "result"), 3u);
}

TEST(StaticMethodSimulation, StaticMethodCallsStaticMethod) {
  EXPECT_EQ(RunAndGet(
      "class Math;\n"
      "  static function int double_it(int x);\n"
      "    return x + x;\n"
      "  endfunction\n"
      "  static function int quad(int x);\n"
      "    return double_it(double_it(x));\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = Math::quad(5);\n"
      "  end\n"
      "endmodule\n", "result"), 20u);
}

TEST(StaticMethodSimulation, StaticMethodSharedAcrossInstances) {
  EXPECT_EQ(RunAndGet(
      "class Id;\n"
      "  static int current;\n"
      "  static function int next_id();\n"
      "    current = current + 1;\n"
      "    return current;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Id a, b;\n"
      "    a = new;\n"
      "    b = new;\n"
      "    a.next_id();\n"
      "    b.next_id();\n"
      "    result = Id::next_id();\n"
      "  end\n"
      "endmodule\n", "result"), 3u);
}

}  // namespace
