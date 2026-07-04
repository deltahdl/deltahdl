#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

// §8.24 full-pipeline: a method whose body is declared out of the class block
// (an `extern` prototype inside the class, the full definition qualified with
// `ClassName::` after the class) must actually EXECUTE end-to-end and return
// the value its out-of-block body computes. The elaborator links the qualified
// definition back onto the class type (AttachCuMethodsToClasses); this drives
// real source through parse+elaborate+lower+run to prove the linked body runs.
TEST(ClassSim, E2eOutOfBlockFunctionBodyExecutes) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  extern function int foo(input int a);\n"
                      "endclass\n"
                      "function int C::foo(input int a);\n"
                      "  return a + 1;\n"
                      "endfunction\n"
                      "module t;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    r = c.foo(41);\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            42u);
}

// §8.24: the same out-of-block linkage for a TASK. The extern task prototype
// lives in the class; the out-of-block body (`task C::set(...)`) assigns a
// class property. An in-block getter reads that property back so the effect of
// the out-of-block task body is observable at module scope.
TEST(ClassSim, E2eOutOfBlockTaskBodyExecutes) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int val;\n"
                      "  extern task set(input int a);\n"
                      "  function int get();\n"
                      "    return val;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "task C::set(input int a);\n"
                      "  val = a;\n"
                      "endtask\n"
                      "module t;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    c.set(7);\n"
                      "    r = c.get();\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            7u);
}

TEST(ClassSim, ExternMethodRegisteredSeparately) {
  SimFixture f;
  auto* type = MakeClassType(f, "MyClass", {"val"});

  auto* extern_method = f.arena.Create<ModuleItem>();
  extern_method->kind = ModuleItemKind::kFunctionDecl;
  extern_method->name = "get_val";
  extern_method->func_body_stmts.push_back(
      MakeReturn(f.arena, MkId(f.arena, "val")));

  type->methods["get_val"] = extern_method;

  auto [handle, obj] = MakeObj(f, type);
  auto* resolved = obj->ResolveMethod("get_val");
  EXPECT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->name, "get_val");
}

TEST(ClassSim, OutOfBlockBodyReplacesPrototype) {
  SimFixture f;
  auto* type = MakeClassType(f, "Packet", {});

  auto* proto = f.arena.Create<ModuleItem>();
  proto->kind = ModuleItemKind::kFunctionDecl;
  proto->name = "send";
  proto->is_extern = true;
  type->methods["send"] = proto;

  auto* body = f.arena.Create<ModuleItem>();
  body->kind = ModuleItemKind::kFunctionDecl;
  body->name = "send";
  body->method_class = "Packet";
  body->func_body_stmts.push_back(MakeReturn(f.arena, MkInt(f.arena, 100)));

  type->methods["send"] = body;

  auto* resolved = type->methods["send"];
  EXPECT_EQ(resolved, body);
  EXPECT_FALSE(resolved->func_body_stmts.empty());
}

TEST(ClassSim, OutOfBlockMethodResolvedViaResolveMethod) {
  SimFixture f;
  auto* type = MakeClassType(f, "C", {"x"});

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "foo";
  method->method_class = "C";
  type->methods["foo"] = method;

  auto [handle, obj] = MakeObj(f, type);
  auto* resolved = obj->ResolveMethod("foo");
  EXPECT_EQ(resolved, method);
}

TEST(ClassSim, OutOfBlockConstructor) {
  SimFixture f;
  auto* type = MakeClassType(f, "C", {});

  auto* ctor = f.arena.Create<ModuleItem>();
  ctor->kind = ModuleItemKind::kFunctionDecl;
  ctor->name = "new";
  ctor->method_class = "C";
  type->methods["new"] = ctor;

  auto it = type->methods.find("new");
  ASSERT_NE(it, type->methods.end());
  EXPECT_EQ(it->second->method_class, "C");
}

TEST(ClassSim, OutOfBlockTaskResolvedViaResolveMethod) {
  SimFixture f;
  auto* type = MakeClassType(f, "C", {});

  auto* task = f.arena.Create<ModuleItem>();
  task->kind = ModuleItemKind::kTaskDecl;
  task->name = "run";
  task->method_class = "C";
  type->methods["run"] = task;

  auto [handle, obj] = MakeObj(f, type);
  auto* resolved = obj->ResolveMethod("run");
  EXPECT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->name, "run");
  EXPECT_EQ(resolved->kind, ModuleItemKind::kTaskDecl);
}

TEST(ClassSim, MultipleOutOfBlockMethodsLinked) {
  SimFixture f;
  auto* type = MakeClassType(f, "C", {"x"});

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "get";
  func->method_class = "C";
  func->func_body_stmts.push_back(MakeReturn(f.arena, MkInt(f.arena, 1)));
  type->methods["get"] = func;

  auto* task = f.arena.Create<ModuleItem>();
  task->kind = ModuleItemKind::kTaskDecl;
  task->name = "set";
  task->method_class = "C";
  type->methods["set"] = task;

  auto [handle, obj] = MakeObj(f, type);
  EXPECT_NE(obj->ResolveMethod("get"), nullptr);
  EXPECT_NE(obj->ResolveMethod("set"), nullptr);
  EXPECT_EQ(obj->ResolveMethod("get")->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(obj->ResolveMethod("set")->kind, ModuleItemKind::kTaskDecl);
}

TEST(ClassSim, UnresolvedMethodReturnsNull) {
  SimFixture f;
  auto* type = MakeClassType(f, "C", {});
  auto [handle, obj] = MakeObj(f, type);
  EXPECT_EQ(obj->ResolveMethod("nonexistent"), nullptr);
}

}  // namespace
