#include <gtest/gtest.h>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "parser/ast_module.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

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

TEST(ClassSim, PackageOutOfBlockStaticFunctionAfterWildcardImport) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class root;\n"
                      "    extern static function int sget();\n"
                      "  endclass\n"
                      "  function int root::sget();\n"
                      "    return 5;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "import p::*;\n"
                      "module t;\n"
                      "  int a;\n"
                      "  initial a = root::sget();\n"
                      "endmodule\n",
                      "a"),
            5u);
}

TEST(ClassSim, PackageOutOfBlockInstanceMethodReadsProperty) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class root;\n"
                      "    int tag = 7;\n"
                      "    extern function int iget();\n"
                      "  endclass\n"
                      "  function int root::iget();\n"
                      "    return tag;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "import p::*;\n"
                      "module t;\n"
                      "  int b;\n"
                      "  initial begin\n"
                      "    static root r = new;\n"
                      "    b = r.iget();\n"
                      "  end\n"
                      "endmodule\n",
                      "b"),
            7u);
}

TEST(ClassSim, PackageOutOfBlockStaticFunctionThroughPackageScope) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class root;\n"
                      "    extern static function int sget();\n"
                      "  endclass\n"
                      "  function int root::sget();\n"
                      "    return 11;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int a;\n"
                      "  initial a = p::root::sget();\n"
                      "endmodule\n",
                      "a"),
            11u);
}

TEST(ClassSim, PackageOutOfBlockStaticMethodReadsStaticProperty) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class cnt;\n"
                      "    static int total = 40;\n"
                      "    extern static function int bump();\n"
                      "  endclass\n"
                      "  function int cnt::bump();\n"
                      "    total = total + 3;\n"
                      "    return total;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "import p::*;\n"
                      "module t;\n"
                      "  int a;\n"
                      "  initial a = cnt::bump();\n"
                      "endmodule\n",
                      "a"),
            43u);
}

TEST(ClassSim, ModuleClassOutOfBlockInstanceMethodReadsProperty) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  class root;\n"
                      "    int tag = 7;\n"
                      "    extern function int iget();\n"
                      "  endclass\n"
                      "  function int root::iget();\n"
                      "    return tag;\n"
                      "  endfunction\n"
                      "  int b;\n"
                      "  initial begin\n"
                      "    static root r = new;\n"
                      "    b = r.iget();\n"
                      "  end\n"
                      "endmodule\n",
                      "b"),
            7u);
}

TEST(ClassSim, ModuleClassOutOfBlockStaticFunctionThroughClassScope) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  class root;\n"
                      "    extern static function int sget();\n"
                      "  endclass\n"
                      "  function int root::sget();\n"
                      "    return 5;\n"
                      "  endfunction\n"
                      "  int a;\n"
                      "  initial a = root::sget();\n"
                      "endmodule\n",
                      "a"),
            5u);
}

TEST(ClassSim, OutOfBlockVirtualMethodTakesPrototypeDefault) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int base = 10;\n"
                      "  extern virtual function int g(int a = 1);\n"
                      "endclass\n"
                      "function int C::g(int a);\n"
                      "  return base + a;\n"
                      "endfunction\n"
                      "module t;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    r = c.g();\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            11u);
}

TEST(ClassSim, OutOfBlockConstructorTakesPrototypeDefault) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int v, w;\n"
                      "  extern function new(int a, int b = 3);\n"
                      "endclass\n"
                      "function C::new(int a, int b);\n"
                      "  v = a * 2;\n"
                      "  w = b;\n"
                      "endfunction\n"
                      "module t;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    static C c = new(7);\n"
                      "    r = c.v * 100 + c.w;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            1403u);
}

TEST(ClassSim, OutOfBlockMethodTakesPrototypeDefaultsAfterFirstGiven) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  extern function int sum(int a, int b = 20,\n"
                      "                          int c = 300);\n"
                      "endclass\n"
                      "function int C::sum(int a, int b, int c);\n"
                      "  return a + b + c;\n"
                      "endfunction\n"
                      "module t;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    r = c.sum(5);\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            325u);
}

TEST(ClassSim, UnresolvedMethodReturnsNull) {
  SimFixture f;
  auto* type = MakeClassType(f, "C", {});
  auto [handle, obj] = MakeObj(f, type);
  EXPECT_EQ(obj->ResolveMethod("nonexistent"), nullptr);
}

TEST(ClassSim, OutOfBlockBodiesAmongModuleItemsAreTheClassMethods) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  class Rect;\n"
                       "    int w, h;\n"
                       "    static int count = 0;\n"
                       "    extern function new(int w, int h);\n"
                       "    extern function int area();\n"
                       "  endclass\n"
                       "  int seen;\n"
                       "  function Rect::new(int w, int h);\n"
                       "    this.w = w; this.h = h; count++;\n"
                       "  endfunction\n"
                       "  function int Rect::area();\n"
                       "    return w * h;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    static Rect a = new(4, 6), b = new(1, 1);\n"
                       "    seen = Rect::count;\n"
                       "    $display(\"area %0d count %0d static %0d\",\n"
                       "             a.area(), seen, b.count);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "area 24 count 2 static 2\n");
}

TEST(ClassSim, OutOfBlockVoidMethodAmongModuleItemsWritesThroughThis) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  class Rect;\n"
                       "    int w, h;\n"
                       "    extern function new(int w, int h);\n"
                       "    extern function int area();\n"
                       "    extern function void setw(int w);\n"
                       "  endclass\n"
                       "  function Rect::new(int w, int h);\n"
                       "    this.w = w; this.h = h;\n"
                       "  endfunction\n"
                       "  function int Rect::area();\n"
                       "    return w * h;\n"
                       "  endfunction\n"
                       "  function void Rect::setw(int w);\n"
                       "    this.w = w;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    static Rect a = new(4, 6);\n"
                       "    a.setw(5);\n"
                       "    $display(\"area %0d\", a.area());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "area 30\n");
}

}  // namespace
