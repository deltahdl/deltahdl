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
  method->is_static_method = true;
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
                                           "    static Outer::Inner i = new;\n"
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
                                           "    static Outer::Inner i = new;\n"
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

static std::string OuterInnerQueueDesign(std::string_view rest) {
  return "class Outer;\n"
         "  class Inner;\n"
         "    int v = 7;\n"
         "  endclass\n"
         "endclass\n" +
         std::string(rest);
}

TEST(ClassScopeResolutionSim, ProceduralQueueOfANestedClassHoldsHandles) {
  EXPECT_EQ(RunAndGet(OuterInnerQueueDesign("module t;\n"
                                            "  int y;\n"
                                            "  initial begin\n"
                                            "    Outer::Inner q[$];\n"
                                            "    static Outer::Inner i = new;\n"
                                            "    q.push_back(i);\n"
                                            "    y = q[0].v;\n"
                                            "  end\n"
                                            "endmodule\n"),
                      "y"),
            7u);
}

TEST(ClassScopeResolutionSim, PropertyQueueOfANestedClassHoldsHandles) {
  EXPECT_EQ(RunAndGet(OuterInnerQueueDesign("class Holder;\n"
                                            "  Outer::Inner q[$];\n"
                                            "endclass\n"
                                            "module t;\n"
                                            "  Holder h = new;\n"
                                            "  int y;\n"
                                            "  initial begin\n"
                                            "    static Outer::Inner i = new;\n"
                                            "    h.q.push_back(i);\n"
                                            "    y = h.q[0].v;\n"
                                            "  end\n"
                                            "endmodule\n"),
                      "y"),
            7u);
}

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

TEST(ClassScopeResolutionSim, ProceduralFixedArrayOfANestedClassHoldsHandles) {
  EXPECT_EQ(RunAndGet(OuterInnerQueueDesign("module t;\n"
                                            "  int y;\n"
                                            "  initial begin\n"
                                            "    Outer::Inner arr[2];\n"
                                            "    Outer::Inner q[$];\n"
                                            "    static Outer::Inner a = new;\n"
                                            "    static Outer::Inner b = new;\n"
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
                      "    static Outer::Inner i = new;\n"
                      "    o.q.push_back(i);\n"
                      "    y = o.q[0].v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            7u);
}

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

TEST(ClassScopeResolutionSim, AssocArrayPropertyOfANestedClassHoldsHandles) {
  EXPECT_EQ(RunAndGet(OuterInnerQueueDesign("class H;\n"
                                            "  Outer::Inner m[string];\n"
                                            "endclass\n"
                                            "module t;\n"
                                            "  H x = new;\n"
                                            "  int y;\n"
                                            "  initial begin\n"
                                            "    x.m[\"k\"] = new;\n"
                                            "    y = x.m[\"k\"].v;\n"
                                            "  end\n"
                                            "endmodule\n"),
                      "y"),
            7u);
}

TEST(ClassScopeResolutionSim, SubroutineVariablesOfAClassStructTypedef) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class P2;\n"
      "    typedef struct { real r; bit [31:0] data; } S;\n"
      "    static function S One(); One.data = 7; One.r = 1.5; endfunction\n"
      "    static function S Two(); S v; v.data = 9; return v; endfunction\n"
      "  endclass\n"
      "  function automatic P2::S f1(); f1.data = 4; endfunction\n"
      "  function automatic int f3(); P2::S v; v.data = 5;\n"
      "    return v.data; endfunction\n"
      "  P2::S y, w, x;\n"
      "  initial begin\n"
      "    y = P2::One(); w = P2::Two(); x = f1();\n"
      "    $display(\"%0d %f %0d %0d %0d\", y.data, y.r, w.data, x.data,\n"
      "             f3());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "7 1.500000 9 4 5\n");
}

TEST(ClassScopeResolutionSim, InheritedStaticMethodThroughTheDerivedScope) {
  auto v = RunAndGet(
      "class Mem #(int K = 1);\n"
      "  static function int sk(); return K; endfunction\n"
      "endclass\n"
      "class E extends Mem #(4);\n"
      "endclass\n"
      "class P;\n"
      "  static function int pk(); return 5; endfunction\n"
      "endclass\n"
      "class Q extends P;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = Q::pk() * 10 + E::sk();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 54u);
}

TEST(ClassScopeTypedefSim, PropertyOfOwnStructureTypedefSelectsMembers) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Box;\n"
                       "  typedef struct { int a; int b; } S;\n"
                       "  typedef struct packed { bit [7:0] a; bit [7:0] b; } "
                       "P;\n"
                       "  S s; P p;\n"
                       "  function void set();\n"
                       "    s.b = 5; s.a = 3; p.b = 8'd7; p.a = 8'd2;\n"
                       "  endfunction\n"
                       "  function void show();\n"
                       "    $display(\"%0d %0d %0d %0d %0d\", s.a, s.b, p.a, "
                       "p.b, $bits(s));\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Box b;\n"
                       "  initial begin b = new; b.set(); b.show(); end\n"
                       "endmodule\n",
                       f),
            "3 5 2 7 64\n");
}

TEST(ClassScopeTypedefSim, PropertyOfBaseClassStructureTypedefSelectsMembers) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Base;\n"
                       "  typedef struct { int a; int b; } S;\n"
                       "endclass\n"
                       "class Der extends Base;\n"
                       "  S s;\n"
                       "  function void set(); s.b = 5; s.a = 3; endfunction\n"
                       "  function void show();\n"
                       "    $display(\"%0d %0d %0d\", s.a, s.b, $bits(s));\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Der d;\n"
                       "  initial begin d = new; d.set(); d.show(); end\n"
                       "endmodule\n",
                       f),
            "3 5 64\n");
}

}  // namespace
