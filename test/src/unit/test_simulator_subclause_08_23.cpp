#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "parser/ast_module.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassScopeResolutionSim, ScopeResolutionStaticLookup) {
  SimFixture f;
  auto* type = MakeClassType(f, "MyClass", {});
  type->static_properties["MAX_SIZE"] = MakeLogic4VecVal(f.arena, 32, 256);

  auto it = type->static_properties.find("MAX_SIZE");
  ASSERT_NE(it, type->static_properties.end());
  EXPECT_EQ(it->second.ToUint64(), 256u);
}

TEST(ClassScopeResolutionSim, ScopeResolutionMethodLookup) {
  SimFixture f;
  auto* type = MakeClassType(f, "Utils", {});
  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "compute";
  method->is_static = true;
  type->methods["compute"] = method;

  auto* found = f.ctx.FindClassType("Utils");
  ASSERT_NE(found, nullptr);
  auto it = found->methods.find("compute");
  ASSERT_NE(it, found->methods.end());
  EXPECT_EQ(it->second->name, "compute");
}

TEST(ClassScopeResolutionSim, ScopeResolutionMissingProperty) {
  SimFixture f;
  auto* type = MakeClassType(f, "Empty", {});
  auto it = type->static_properties.find("nonexistent");
  EXPECT_EQ(it, type->static_properties.end());
}

TEST(ClassScopeResolutionSim, ScopeResolutionDisambiguates) {
  SimFixture f;
  auto* type = MakeClassType(f, "Base", {});
  type->static_properties["bin"] = MakeLogic4VecVal(f.arena, 32, 42);

  auto* local = f.ctx.CreateLocalVariable("bin", 32);
  local->value = MakeLogic4VecVal(f.arena, 32, 123);

  auto it = type->static_properties.find("bin");
  ASSERT_NE(it, type->static_properties.end());
  EXPECT_EQ(it->second.ToUint64(), 42u);
  EXPECT_EQ(local->value.ToUint64(), 123u);
}

TEST(ClassScopeResolutionSim, ScopeResolutionBaseClassStatic) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});
  base->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 7);

  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;

  auto* found = f.ctx.FindClassType("Base");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->static_properties["count"].ToUint64(), 7u);
}

TEST(ClassScopeResolutionSim, ScopeResolutionCallReturnsValue) {
  EXPECT_EQ(RunAndGet("class Util;\n"
                      "  static function int answer();\n"
                      "    return 42;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = Util::answer();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(ClassScopeResolutionSim, StaticPropertyReadViaScope) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int count;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = C::count;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

TEST(ClassScopeResolutionSim, StaticPropertyReadWithInit) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int val = 99;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = C::val;\n"
                      "endmodule\n",
                      "result"),
            99u);
}

TEST(ClassScopeResolutionSim, StaticMethodWithArgs) {
  EXPECT_EQ(RunAndGet("class Math;\n"
                      "  static function int add(int a, int b);\n"
                      "    return a + b;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = Math::add(10, 25);\n"
                      "endmodule\n",
                      "result"),
            35u);
}

TEST(ClassScopeResolutionSim, StaticVoidMethodCall) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int x;\n"
                      "  static function void set_x(int v);\n"
                      "    x = v;\n"
                      "  endfunction\n"
                      "  static function int get_x();\n"
                      "    return x;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C::set_x(77);\n"
                      "    result = C::get_x();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            77u);
}

TEST(ClassScopeResolutionSim, DisambiguatesClassScopeFromLocal) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  static int val = 42;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int val = 100;\n"
                      "  int result;\n"
                      "  initial result = Base::val;\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(ClassScopeResolutionSim, UnknownClassTypeReturnsDefault) {
  SimFixture f;
  auto* found = f.ctx.FindClassType("Nonexistent");
  EXPECT_EQ(found, nullptr);
}

TEST(ClassScopeResolutionSim, NestedClassTypeDistinct) {
  SimFixture f;
  auto* list_type = MakeClassType(f, "StringList", {});
  auto* tree_type = MakeClassType(f, "StringTree", {});

  auto* list_node = MakeClassType(f, "StringList::Node", {});
  list_node->properties.push_back({"name", 32, false});

  auto* tree_node = MakeClassType(f, "StringTree::Node", {});
  tree_node->properties.push_back({"name", 32, false});
  tree_node->properties.push_back({"left", 32, false});

  EXPECT_NE(f.ctx.FindClassType("StringList::Node"),
            f.ctx.FindClassType("StringTree::Node"));
  EXPECT_EQ(list_node->properties.size(), 1u);
  EXPECT_EQ(tree_node->properties.size(), 2u);
  (void)list_type;
  (void)tree_type;
}

TEST(ClassScopeResolutionSim, StaticPropertyLoweredFromDecl) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Config;\n"
      "  static int WIDTH = 8;\n"
      "  static int DEPTH = 16;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = Config::WIDTH;\n"
      "    r2 = Config::DEPTH;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 8u}, {"r2", 16u}});
}

TEST(ClassScopeResolutionSim, SuperclassStaticAccessFromDerived) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  static int shared = 55;\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  static function int get_shared();\n"
                      "    return Base::shared;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = Derived::get_shared();\n"
                      "endmodule\n",
                      "result"),
            55u);
}

TEST(ClassScopeResolutionSim, StaticPropertyWrittenViaScope) {
  // C8: class-scope-resolved static property written in an assignment, then
  // read back through the same `::` access -- full pipeline.
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int count;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C::count = 5;\n"
                      "    result = C::count;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            5u);
}

TEST(ClassScopeResolutionSim, EnumNamedConstantViaScope) {
  // C8: enumeration named constant reachable via `::` -- full pipeline.
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  typedef enum { RED, GREEN = 3, BLUE } color_e;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = C::GREEN;\n"
                      "endmodule\n",
                      "result"),
            3u);
}

// §8.23 (printed page 200-201 of the LRM): a class declared inside another
// is a type of its own, named `Outer::Inner` from outside, whose objects have
// their own properties and methods. `int v = 5` reading 0 and `twice()` 0 is
// the object built with no class behind it, so the product cannot be 510 by
// accident.
TEST(ClassScopeResolutionSim, ModuleScopeNestedObjectPropertyAndMethod) {
  EXPECT_EQ(RunAndGet("class Outer;\n"
                      "  class Inner;\n"
                      "    int v = 5;\n"
                      "    function int twice(); return v * 2; endfunction\n"
                      "  endclass\n"
                      "endclass\n"
                      "module t;\n"
                      "  Outer::Inner in = new;\n"
                      "  int r;\n"
                      "  initial r = in.v * 100 + in.twice();\n"
                      "endmodule\n",
                      "r"),
            510u);
}

// §8.23: inside the containing class the nested class is named bare, both by
// a method's local `Inner i = new` and by a property `Inner mine` the
// constructor builds with `mine = new`. 8 is `i.v = 4` doubled and 5 the
// property's initializer read through `mine`; a local or a property with no
// class behind it answers 0 for either.
TEST(ClassScopeResolutionSim, NestedObjectBuiltInsideAnOuterMethod) {
  EXPECT_EQ(RunAndGet("class Outer;\n"
                      "  class Inner;\n"
                      "    int v = 5;\n"
                      "    function int twice(); return v * 2; endfunction\n"
                      "  endclass\n"
                      "  Inner mine;\n"
                      "  function new(); mine = new; endfunction\n"
                      "  function int useInner();\n"
                      "    Inner i = new;\n"
                      "    i.v = 4;\n"
                      "    return i.twice();\n"
                      "  endfunction\n"
                      "  function int mineV(); return mine.v; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  Outer o = new;\n"
                      "  int r;\n"
                      "  initial r = o.useInner() * 10 + o.mineV();\n"
                      "endmodule\n",
                      "r"),
            85u);
}

// §8.23's Outer/Inner example: a nested class's method has lexically scoped,
// unqualified access to the containing class's static properties, the local
// one included, and reaches a non-static one only through a handle. 7, 4 and
// 9 are the three initializers; each digit that reads 0 is a lookup that did
// not reach the containing class.
TEST(ClassScopeResolutionSim, NestedMethodReadsTheContainingClassStatics) {
  EXPECT_EQ(RunAndGet("class Outer;\n"
                      "  int outerProp = 9;\n"
                      "  static int outerStaticProp = 7;\n"
                      "  static local int outerLocalStaticProp = 4;\n"
                      "  class Inner;\n"
                      "    function int readStatic();\n"
                      "      return outerStaticProp;\n"
                      "    endfunction\n"
                      "    function int readOuter(Outer h);\n"
                      "      return h.outerProp;\n"
                      "    endfunction\n"
                      "    function int readLocal();\n"
                      "      return outerLocalStaticProp;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endclass\n"
                      "module t;\n"
                      "  Outer::Inner in = new;\n"
                      "  Outer o = new;\n"
                      "  int r;\n"
                      "  initial r = in.readStatic() * 100 +\n"
                      "              in.readLocal() * 10 + in.readOuter(o);\n"
                      "endmodule\n",
                      "r"),
            749u);
}

// §8.23's `outerStaticProp = 0` in innerMethod: the unqualified name written
// from the nested class's method is the containing class's own storage, which
// `Outer::outerStaticProp` then reads. 31 is neither the initializer nor a
// write that landed on the nested object.
TEST(ClassScopeResolutionSim, NestedMethodWritesTheContainingClassStatic) {
  EXPECT_EQ(RunAndGet("class Outer;\n"
                      "  static int outerStaticProp = 7;\n"
                      "  class Inner;\n"
                      "    function void innerMethod();\n"
                      "      outerStaticProp = 31;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endclass\n"
                      "module t;\n"
                      "  Outer::Inner in = new;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    in.innerMethod();\n"
                      "    r = Outer::outerStaticProp;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            31u);
}

// §8.23's StringList/Node example, with a depth and a push that links each
// new node ahead of the head: after pushing "beta" then "alpha" the head is
// the "alpha" node at depth 2, linked to the "beta" node at depth 1. A Node
// built with no class behind it holds neither name nor depth, reading "" and
// 0 for every line.
TEST(ClassScopeResolutionSim, StringListNodeExampleLinksNestedObjects) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class StringList;\n"
      "  class Node;\n"
      "    string name;\n"
      "    Node link;\n"
      "    int depth;\n"
      "  endclass\n"
      "  Node head;\n"
      "  function void push(string s);\n"
      "    Node n = new;\n"
      "    n.name = s;\n"
      "    n.link = head;\n"
      "    n.depth = head == null ? 1 : head.depth + 1;\n"
      "    head = n;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  StringList l = new;\n"
      "  int head_depth, link_depth;\n"
      "  bit head_is_alpha;\n"
      "  initial begin\n"
      "    l.push(\"beta\");\n"
      "    l.push(\"alpha\");\n"
      "    head_depth = l.head.depth;\n"
      "    link_depth = l.head.link.depth;\n"
      "    head_is_alpha = l.head.name == \"alpha\";\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"head_depth", 2u}, {"link_depth", 1u}, {"head_is_alpha", 1u}});
}

// §8.23 (printed pages 200-201 of the LRM): from outside the containing
// class the nested class is named `Outer::Inner`, and a nested class's
// method has unqualified access to the containing class's static
// properties. The three tests below declare such an object as a subroutine
// body's local -- a module function's, a task's and a class method's --
// which CreateFuncLocalVar (eval_function_body.cpp) creates, where a
// procedural block's declaration goes through TryExecClassVarDecl. Looked
// up by the bare `Inner`, the local was a plain variable, `i.bump()` ran
// nothing and `Outer::n` stayed 0; through the `Outer::Inner` key
// LowerNestedClass registers, bump() adds 5. The shared Outer/Inner
// prelude is one string so the three do not repeat it.
static std::string OuterInnerBumpDesign(std::string_view rest) {
  return "class Outer;\n"
         "  static int n = 0;\n"
         "  class Inner;\n"
         "    function void bump(); n = n + 5; endfunction\n"
         "  endclass\n"
         "endclass\n" +
         std::string(rest);
}

TEST(ClassScopeResolutionSim, ModuleFunctionLocalOfANestedClassIsConstructed) {
  EXPECT_EQ(RunAndGet(OuterInnerBumpDesign("module t;\n"
                                           "  function int f();\n"
                                           "    Outer::Inner i = new;\n"
                                           "    i.bump();\n"
                                           "    return Outer::n;\n"
                                           "  endfunction\n"
                                           "  int r;\n"
                                           "  initial r = f();\n"
                                           "endmodule\n"),
                      "r"),
            5u);
}

TEST(ClassScopeResolutionSim, TaskLocalOfANestedClassIsConstructed) {
  EXPECT_EQ(RunAndGet(OuterInnerBumpDesign("module t;\n"
                                           "  int r;\n"
                                           "  task bump_once();\n"
                                           "    Outer::Inner i = new;\n"
                                           "    i.bump();\n"
                                           "    r = Outer::n;\n"
                                           "  endtask\n"
                                           "  initial bump_once();\n"
                                           "endmodule\n"),
                      "r"),
            5u);
}

TEST(ClassScopeResolutionSim, ClassMethodLocalOfANestedClassIsConstructed) {
  EXPECT_EQ(RunAndGet(OuterInnerBumpDesign("class Driver;\n"
                                           "  function int go();\n"
                                           "    Outer::Inner i = new;\n"
                                           "    i.bump();\n"
                                           "    return Outer::n;\n"
                                           "  endfunction\n"
                                           "endclass\n"
                                           "module t;\n"
                                           "  Driver d = new;\n"
                                           "  int r;\n"
                                           "  initial r = d.go();\n"
                                           "endmodule\n"),
                      "r"),
            5u);
}

// §8.23 (printed pages 200-201), §7.10 (printed 169) and §8.4 (printed 181):
// a queue whose element type is the nested class named `Outer::Inner` holds
// handles, so `q[0].v` reads the property of the object the element refers
// to. The two tests share the Outer/Inner prelude and read 7, Inner's `v`
// initializer: a queue of plain values answers 0 for `q[0].v`, and so does a
// declaration that built no queue at all.
static std::string OuterInnerQueueDesign(std::string_view rest) {
  return "class Outer;\n"
         "  class Inner;\n"
         "    int v = 7;\n"
         "  endclass\n"
         "endclass\n" +
         std::string(rest);
}

// A procedural declaration in an initial block: ExecVarDeclImpl
// (statement_assign_decl.cpp) took `Outer::Inner q[$]` for a scalar handle
// once DeclaredClassKey named the class, building no queue, and
// CreateBlockQueue had flagged the queue by the bare `Inner`.
TEST(ClassScopeResolutionSim, ProceduralQueueOfANestedClassHoldsHandles) {
  EXPECT_EQ(RunAndGet(OuterInnerQueueDesign("module t;\n"
                                            "  int y;\n"
                                            "  initial begin\n"
                                            "    Outer::Inner q[$];\n"
                                            "    Outer::Inner i = new;\n"
                                            "    q.push_back(i);\n"
                                            "    y = q[0].v;\n"
                                            "  end\n"
                                            "endmodule\n"),
                      "y"),
            7u);
}

// A class property of another class: ElementTypeIsClass
// (eval_array_class_queue.cpp) asked for the bare `Inner` where the
// declaration wrote `Outer::Inner`, so the property's queue held plain values
// and `h.q[0].v` read 0.
TEST(ClassScopeResolutionSim, PropertyQueueOfANestedClassHoldsHandles) {
  EXPECT_EQ(RunAndGet(OuterInnerQueueDesign("class Holder;\n"
                                            "  Outer::Inner q[$];\n"
                                            "endclass\n"
                                            "module t;\n"
                                            "  Holder h = new;\n"
                                            "  int y;\n"
                                            "  initial begin\n"
                                            "    Outer::Inner i = new;\n"
                                            "    h.q.push_back(i);\n"
                                            "    y = h.q[0].v;\n"
                                            "  end\n"
                                            "endmodule\n"),
                      "y"),
            7u);
}

// §7.8 (printed page 163) declares an associative array by its index type
// whatever the element type, and §8.4 (printed 181) makes each element of
// one declared with a class's name a handle, constructed by `new` into the
// entry (§7.8.1). Declared in an initial block with the nested class's
// scoped name, TryExecClassVarDecl (statement_assign_decl.cpp) took
// `Outer::Inner aa[string]` for one scalar handle and built no array, so
// `aa["k"] = new` constructed nothing and `aa["k"].v` read 0.
TEST(ClassScopeResolutionSim, ProceduralAssocArrayOfANestedClassHoldsHandles) {
  EXPECT_EQ(RunAndGet(OuterInnerQueueDesign("module t;\n"
                                            "  int y;\n"
                                            "  initial begin\n"
                                            "    Outer::Inner aa[string];\n"
                                            "    aa[\"k\"] = new;\n"
                                            "    y = aa[\"k\"].v;\n"
                                            "  end\n"
                                            "endmodule\n"),
                      "y"),
            7u);
}

// §7.4.2 (printed pages 153-154) declares a fixed-size array by its range
// whatever the element type, so `Outer::Inner arr[2]` in an initial block is
// two elements each holding a handle (§8.4, printed 181). Taken for one
// scalar handle, `arr[0] = b` set one bit of it, and what the queue then
// received from `arr[0]` was that bit, no handle: 97 is b's 9 then a's 7
// read back through the queue, where the scalar's bits gave a null handle
// and at most a's 7.
TEST(ClassScopeResolutionSim, ProceduralFixedArrayOfANestedClassHoldsHandles) {
  EXPECT_EQ(RunAndGet(OuterInnerQueueDesign("module t;\n"
                                            "  int y;\n"
                                            "  initial begin\n"
                                            "    Outer::Inner arr[2];\n"
                                            "    Outer::Inner q[$];\n"
                                            "    Outer::Inner a = new;\n"
                                            "    Outer::Inner b = new;\n"
                                            "    b.v = 9;\n"
                                            "    arr[0] = b;\n"
                                            "    arr[1] = a;\n"
                                            "    q.push_back(arr[0]);\n"
                                            "    q.push_back(arr[1]);\n"
                                            "    y = q[0].v * 10 + q[1].v;\n"
                                            "  end\n"
                                            "endmodule\n"),
                      "y"),
            97u);
}

// §8.23 (printed pages 200-201): the nested class's bare name is visible
// throughout the containing class, so Outer's own property `Inner q[$]` is a
// queue of Outer::Inner handles. The queue is built on its first reference,
// here from the module's initial block, where no method of Outer is running:
// ElementTypeIsClass (eval_array_class_queue.cpp) asked SimContext's lookup,
// which resolves a bare nested name through the running method's class
// alone, so the property held plain values and `o.q[0].v` read 0.
TEST(ClassScopeResolutionSim,
     BareNestedNameQueuePropertyFirstReferencedFromAModule) {
  EXPECT_EQ(RunAndGet("class Outer;\n"
                      "  class Inner;\n"
                      "    int v = 7;\n"
                      "  endclass\n"
                      "  Inner q[$];\n"
                      "endclass\n"
                      "module t;\n"
                      "  Outer o = new;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    Outer::Inner i = new;\n"
                      "    o.q.push_back(i);\n"
                      "    y = o.q[0].v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            7u);
}

// §8.23 (printed pages 200-201) with §8.4 (printed 181): a property of
// another class declared with the nested class's scoped name is a handle of
// Outer::Inner, so `x.h = new` constructs one and `x.h.v` reads its 7.
// PropertyClassName (eval_array_class_assoc.cpp) resolved the property's
// class by the bare `Inner`, which names no class outside Outer, so
// TryMemberClassNewAssign declined, the generic assignment stored no object,
// and the read answered 0.
TEST(ClassScopeResolutionSim, HandlePropertyOfANestedClassIsConstructed) {
  EXPECT_EQ(RunAndGet(OuterInnerQueueDesign("class H;\n"
                                            "  Outer::Inner h;\n"
                                            "endclass\n"
                                            "module t;\n"
                                            "  H x = new;\n"
                                            "  int y;\n"
                                            "  initial begin\n"
                                            "    x.h = new;\n"
                                            "    y = x.h.v;\n"
                                            "  end\n"
                                            "endmodule\n"),
                      "y"),
            7u);
}

// §7.4.2 (printed pages 153-154): the array property `Outer::Inner kids[2]`
// holds two handles, each constructed by `new` into its element and read
// through it. ElementsAreHandles (eval_class_array_handles.cpp) asked for the
// bare `Inner`, so the elements were plain values: nothing was constructed
// and `x.kids[1].v` read 0.
TEST(ClassScopeResolutionSim, ArrayPropertyOfANestedClassHoldsHandles) {
  EXPECT_EQ(RunAndGet(OuterInnerQueueDesign("class H;\n"
                                            "  Outer::Inner kids[2];\n"
                                            "endclass\n"
                                            "module t;\n"
                                            "  H x = new;\n"
                                            "  int y;\n"
                                            "  initial begin\n"
                                            "    x.kids[1] = new;\n"
                                            "    y = x.kids[1].v;\n"
                                            "  end\n"
                                            "endmodule\n"),
                      "y"),
            7u);
}

// §8.23: inside Outer the nested class is named bare, so Outer's property
// `Inner h` is a handle of Outer::Inner, constructed from a module by `o.h =
// new` where no method of Outer runs. The bare name was resolved through the
// running method's class alone, so the property named no class from the
// module and `o.h.v` read 0.
TEST(ClassScopeResolutionSim,
     BareNestedNameHandlePropertyConstructedFromAModule) {
  EXPECT_EQ(RunAndGet("class Outer;\n"
                      "  class Inner;\n"
                      "    int v = 7;\n"
                      "  endclass\n"
                      "  Inner h;\n"
                      "endclass\n"
                      "module t;\n"
                      "  Outer o = new;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    o.h = new;\n"
                      "    y = o.h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            7u);
}

}  // namespace
