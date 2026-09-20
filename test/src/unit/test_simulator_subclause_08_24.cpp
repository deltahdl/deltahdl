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

// §8.24 with §26.3: an out-of-block declaration stands in the same scope as
// its class, so a class a package declares has its bodies among the package's
// items, and they must be attached to the class whether it is reached through
// a wildcard import or through `p::C`. Before the bodies were attached the
// in-class prototype answered every call with 0, which each value below
// differs from.
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
                      "    root r = new;\n"
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

// §8.9 with §8.24: the static-ness of the prototype is carried onto the body,
// so the body is called without an object and reads the static property
// through the class, 3 added to its initial 40 where an unattached body or a
// non-static one gives 0.
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

// §8.24 with §23.9: a class declared inside a module has its out-of-block
// bodies among the module's items, the scope the class is declared in, and
// they are attached to the class as the compilation unit's and a package's
// are. An instance body reads a property and a static one is called through
// the class; the prototype alone gives 0 for each.
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
                      "    root r = new;\n"
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

// §8.24: a default argument value is given in the `extern` prototype and may
// be omitted from the out-of-block declaration; §13.5.3 has a call that omits
// the argument take that default. The body replacing the prototype must keep
// the prototype's default, or `c.g()` reads `a` as 0 and answers 10.
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
                      "    C c = new;\n"
                      "    r = c.g();\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            11u);
}

// §8.24 for the constructor: `new(7)` against `extern function new(int a,
// int b = 3)` whose out-of-block body names no default leaves `w` 3, not 0.
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
                      "    C c = new(7);\n"
                      "    r = c.v * 100 + c.w;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            1403u);
}

// §8.24 and §13.5.3: two trailing defaults in the prototype of a non-virtual
// method, the call giving the first argument alone; each omitted argument
// takes its own default, so the sum is 5 + 20 + 300 rather than 5.
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
                      "    C c = new;\n"
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

}  // namespace
