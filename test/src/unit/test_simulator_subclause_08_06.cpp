#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "builders_ast.h"
#include "builders_systask.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "parser/ast_module.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ObjectMethodSim, SimpleMethodCall) {
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

TEST(ObjectMethodSim, MethodNotFound) {
  SimFixture f;
  auto* type = MakeClassType(f, "Simple", {});
  auto [handle, obj] = MakeObj(f, type);

  auto* resolved = obj->ResolveMethod("nonexistent");
  EXPECT_EQ(resolved, nullptr);
}

TEST(ObjectMethodSim, MethodCallReturnValue) {
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

TEST(ObjectMethodSim, MethodCallModifiesProperty) {
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

TEST(ObjectMethodSim, ClassMethodLifetimeIsAutomatic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  function int step();\n"
      "    int x;\n"
      "    x = x + 1;\n"
      "    return x;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int a, b, c;\n"
      "  initial begin\n"
      "    C obj;\n"
      "    obj = new;\n"
      "    a = obj.step();\n"
      "    b = obj.step();\n"
      "    c = obj.step();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 1u}, {"c", 1u}});
}

TEST(ObjectMethodSim, MultipleMethodsSameObject) {
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

TEST(ObjectMethodSim, TaskMethodLifetimeIsAutomatic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int acc;\n"
      "  task step();\n"
      "    int x;\n"
      "    x = x + 1;\n"
      "    acc = x;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  int a, b, c;\n"
      "  initial begin\n"
      "    C o;\n"
      "    o = new;\n"
      "    o.step();\n"
      "    a = o.acc;\n"
      "    o.step();\n"
      "    b = o.acc;\n"
      "    o.step();\n"
      "    c = o.acc;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 1u}, {"c", 1u}});
}

TEST(ObjectMethodSim, BarePropertyNameBeatsTheModulesSameNamedVariable) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int sum, i;\n"
                      "  function void run();\n"
                      "    sum = 5;\n"
                      "    for (i = 0; i < 3; i = i + 1) ;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  C h;\n"
                      "  int sum, i;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    h = new;\n"
                      "    h.run();\n"
                      "    result = h.sum * 1000 + h.i * 100 + sum * 10 + i;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            5300u);
}

TEST(ObjectMethodSim,
     BarePropertyReadBeatsTheModulesVariableAndALocalBeatsBoth) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int tag = 7;\n"
                      "  function int prop(); return tag; endfunction\n"
                      "  function int local_one();\n"
                      "    int tag = 4;\n"
                      "    return tag;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int tag = 9;\n"
                      "  C h;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    h = new;\n"
                      "    result = h.prop() * 10 + h.local_one();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            74u);
}

TEST(ObjectMethodSim, MethodCalledOnAClassVariableAProgramDeclares) {
  EXPECT_EQ(RunAndGet("class Cnt;\n"
                      "  int v;\n"
                      "  function new(int s); v = s; endfunction\n"
                      "  function int inc(); v = v + 1; return v; endfunction\n"
                      "endclass\n"
                      "program p;\n"
                      "  Cnt c = new(20);\n"
                      "  int r;\n"
                      "  initial r = c.inc() * 100 + c.v;\n"
                      "endprogram\n"
                      "module t;\n"
                      "  p pr();\n"
                      "endmodule\n",
                      "pr.r"),
            2121u);
}

TEST(ObjectMethodSim, MethodCalledOnAClassVariableAGenerateBlockDeclares) {
  EXPECT_EQ(RunAndGet("class Cnt;\n"
                      "  int v;\n"
                      "  function new(int s); v = s; endfunction\n"
                      "  function int inc(); v = v + 1; return v; endfunction\n"
                      "  function int get(); return v; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int r;\n"
                      "  genvar g;\n"
                      "  generate for (g = 0; g < 2; g++) begin : blk\n"
                      "    Cnt c = new(5);\n"
                      "    initial begin\n"
                      "      if (g == 1) void'(c.inc());\n"
                      "      #1;\n"
                      "      if (g == 0) r = r + c.get();\n"
                      "      else r = r + 100 * c.get();\n"
                      "    end\n"
                      "  end endgenerate\n"
                      "endmodule\n",
                      "r"),
            605u);
}

TEST(ObjectMethodSim,
     MethodCalledOnAClassVariableAnInterfaceDeclaresAndItsPropertyRead) {
  EXPECT_EQ(RunAndGet("class Cnt;\n"
                      "  int v;\n"
                      "  function new(int s); v = s; endfunction\n"
                      "  function int inc(); v = v + 1; return v; endfunction\n"
                      "endclass\n"
                      "interface ifc;\n"
                      "  Cnt c = new(12);\n"
                      "  int r;\n"
                      "  initial r = c.inc();\n"
                      "endinterface\n"
                      "module t;\n"
                      "  ifc i();\n"
                      "  int res;\n"
                      "  initial #1 res = i.r * 100 + i.c.v;\n"
                      "endmodule\n",
                      "res"),
            1313u);
}

TEST(ObjectMethodSim,
     ModuleClassMethodInlineUnionFormalReadsANestedTypedefMember) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef struct { int a, b; } pair_t;\n"
                      "  class C;\n"
                      "    function int f(union tagged { void None; pair_t Add;"
                      " } a);\n"
                      "      return a.Add.a * 10 + a.Add.b;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "  C h;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    h = new;\n"
                      "    y = h.f(tagged Add '{3, 4});\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            34u);
}

TEST(ObjectMethodSim,
     PackageClassMethodInlineUnionFormalReadsANestedTypedefMember) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef struct { int x, y; } xy_t;\n"
                      "  class Geo;\n"
                      "    function int sum(union tagged { void Nil; xy_t Pt; }"
                      " v);\n"
                      "      return v.Pt.x * 10 + v.Pt.y;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "import p::*;\n"
                      "module t;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    static Geo q = new;\n"
                      "    r = q.sum(tagged Pt '{5, 6});\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            56u);
}

TEST(ObjectMethodSim,
     UnitClassMethodInlineUnionFormalReadsAClassTypedefMember) {
  EXPECT_EQ(RunAndGet("class K;\n"
                      "  typedef struct { int hi, lo; } duo_t;\n"
                      "  function int m(union tagged { void One; duo_t Two; }"
                      " d);\n"
                      "    return d.Two.hi * 10 + d.Two.lo;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  K k;\n"
                      "  int z;\n"
                      "  initial begin\n"
                      "    k = new;\n"
                      "    z = k.m(tagged Two '{7, 8});\n"
                      "  end\n"
                      "endmodule\n",
                      "z"),
            78u);
}

TEST(ObjectMethodSim,
     ModuleClassMethodFormalReadsATypedefDefinedBelowTheClass) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef struct pair_t;\n"
                      "  class C;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 10 + a.A.b;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "  typedef struct { int a, b; } pair_t;\n"
                      "  C h;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    h = new;\n"
                      "    y = h.f(tagged A '{3, 4});\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            34u);
}

static std::string ElementMethodDesign(std::string_view rest) {
  return "class C;\n"
         "  int v = 7;\n"
         "  function int get(); return v; endfunction\n"
         "  task run(); v = v + 1; endtask\n"
         "endclass\n" +
         std::string(rest);
}

TEST(ObjectMethodSim, MethodCalledThroughAnElementOfADeclaredArrayRuns) {
  EXPECT_EQ(RunAndGet(ElementMethodDesign("module t;\n"
                                          "  C arr[2];\n"
                                          "  int y;\n"
                                          "  initial begin\n"
                                          "    arr[0] = new;\n"
                                          "    y = arr[0].get();\n"
                                          "  end\n"
                                          "endmodule\n"),
                      "y"),
            7u);
}

TEST(ObjectMethodSim, MethodCalledThroughAQueueElementRuns) {
  EXPECT_EQ(RunAndGet(ElementMethodDesign("module t;\n"
                                          "  C q[$];\n"
                                          "  int y;\n"
                                          "  initial begin\n"
                                          "    static C c = new;\n"
                                          "    q.push_back(c);\n"
                                          "    y = q[0].get();\n"
                                          "  end\n"
                                          "endmodule\n"),
                      "y"),
            7u);
}

TEST(ObjectMethodSim, TaskEnabledThroughAnElementOfADeclaredArrayRuns) {
  EXPECT_EQ(RunAndGet(ElementMethodDesign("module t;\n"
                                          "  C arr[2];\n"
                                          "  int y;\n"
                                          "  initial begin\n"
                                          "    arr[1] = new;\n"
                                          "    arr[1].run();\n"
                                          "    y = arr[1].get();\n"
                                          "  end\n"
                                          "endmodule\n"),
                      "y"),
            8u);
}

TEST(ObjectMethodSim, MethodCalledThroughAChainedPropertyReceiverRuns) {
  EXPECT_EQ(RunAndGet(ElementMethodDesign("class H;\n"
                                          "  C kid = new;\n"
                                          "endclass\n"
                                          "module t;\n"
                                          "  H h = new;\n"
                                          "  int y;\n"
                                          "  initial y = h.kid.get();\n"
                                          "endmodule\n"),
                      "y"),
            7u);
}

TEST(ObjectMethodSim, MethodCalledThroughAnElementsPropertyReceiverRuns) {
  EXPECT_EQ(RunAndGet(ElementMethodDesign("class H;\n"
                                          "  C kid = new;\n"
                                          "endclass\n"
                                          "module t;\n"
                                          "  H arr[2];\n"
                                          "  int y;\n"
                                          "  initial begin\n"
                                          "    arr[0] = new;\n"
                                          "    y = arr[0].kid.get();\n"
                                          "  end\n"
                                          "endmodule\n"),
                      "y"),
            7u);
}

TEST(ObjectMethodSim, MethodCalledThroughAnElementOfAnArrayPropertyRuns) {
  EXPECT_EQ(RunAndGet(ElementMethodDesign("class H;\n"
                                          "  C kids[2];\n"
                                          "endclass\n"
                                          "module t;\n"
                                          "  H h = new;\n"
                                          "  int y;\n"
                                          "  initial begin\n"
                                          "    h.kids[0] = new;\n"
                                          "    h.kids[1] = new;\n"
                                          "    h.kids[1].run();\n"
                                          "    y = h.kids[1].get() * 10 + "
                                          "h.kids[0].get();\n"
                                          "  end\n"
                                          "endmodule\n"),
                      "y"),
            87u);
}

TEST(ObjectMethodSim, MethodCalledThroughACallResultReceiverRuns) {
  EXPECT_EQ(RunAndGet(ElementMethodDesign(
                          "class H;\n"
                          "  C kid = new;\n"
                          "  function C get_kid(); return kid; endfunction\n"
                          "endclass\n"
                          "module t;\n"
                          "  H h = new;\n"
                          "  int y;\n"
                          "  initial y = h.get_kid().get();\n"
                          "endmodule\n"),
                      "y"),
            7u);
}

static std::string CallResultReceiverDesign(std::string_view body) {
  return ElementMethodDesign(
      "module t;\n"
      "  int calls;\n"
      "  C k = new;\n"
      "  int q[$] = '{1, 2};\n"
      "  typedef int iq[$];\n"
      "  function C pk(); calls++; return k; endfunction\n"
      "  function string ps(); calls++; return \"abc\"; endfunction\n"
      "  function iq pq(); calls++; return q; endfunction\n"
      "  int y;\n"
      "  initial begin\n" +
      std::string(body) +
      "    y = calls * 100 + k.v;\n"
      "  end\n"
      "endmodule\n");
}

TEST(ObjectMethodSim, FunctionMethodStatementOnACallResultEvaluatesItOnce) {
  EXPECT_EQ(RunAndGet(CallResultReceiverDesign("    pk().get();\n"), "y"),
            107u);
}

TEST(ObjectMethodSim, TaskMethodStatementOnACallResultEvaluatesItOnce) {
  EXPECT_EQ(RunAndGet(CallResultReceiverDesign("    pk().run();\n"), "y"),
            108u);
}

TEST(ObjectMethodSim, BuiltInMethodStatementOnACallResultEvaluatesItOnce) {
  EXPECT_EQ(RunAndGet(CallResultReceiverDesign("    pk().randomize();\n"
                                               "    pk().srandom(3);\n"),
                      "y"),
            207u);
}

TEST(ObjectMethodSim, StringMethodStatementOnACallResultEvaluatesItOnce) {
  EXPECT_EQ(RunAndGet(CallResultReceiverDesign("    ps().len();\n"), "y"),
            107u);
}

TEST(ObjectMethodSim, QueueMethodStatementOnACallResultEvaluatesItOnce) {
  EXPECT_EQ(RunAndGet(CallResultReceiverDesign("    pq().size();\n"), "y"),
            107u);
}

static std::string MemberOfCallResultDesign(std::string_view body) {
  return ElementMethodDesign(
      "class K;\n"
      "  C kid = new;\n"
      "  C a[2];\n"
      "  function new(); a[0] = new; a[1] = new; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int calls;\n"
      "  K k = new;\n"
      "  function K pk(); calls++; return k; endfunction\n"
      "  int y;\n"
      "  initial begin\n" +
      std::string(body) +
      "    y = calls * 100 + k.kid.v * 10 + k.a[1].v;\n"
      "  end\n"
      "endmodule\n");
}

TEST(ObjectMethodSim, MethodThroughAMemberOfACallResultEvaluatesItOnce) {
  EXPECT_EQ(RunAndGet(MemberOfCallResultDesign("    void'(pk().kid.get());\n"
                                               "    void'(pk().a[1].get());\n"),
                      "y"),
            277u);
}

TEST(ObjectMethodSim,
     MethodStatementThroughAMemberOfACallResultEvaluatesItOnce) {
  EXPECT_EQ(RunAndGet(MemberOfCallResultDesign("    pk().kid.get();\n"
                                               "    pk().kid.run();\n"
                                               "    pk().a[1].get();\n"
                                               "    pk().a[1].run();\n"),
                      "y"),
            488u);
}

TEST(ObjectMethodSim, ARecursiveEvaluationOfTheSameReceiverRunsItsOwnCall) {
  EXPECT_EQ(
      RunAndGet("module t;\n"
                "  int calls;\n"
                "  class C;\n"
                "    function int step(int n); return depth(n); endfunction\n"
                "  endclass\n"
                "  class K; C kid = new; endclass\n"
                "  K k = new;\n"
                "  function K pk(); calls++; return k; endfunction\n"
                "  function int depth(int n);\n"
                "    return n == 0 ? 0 : 1 + pk().kid.step(n - 1);\n"
                "  endfunction\n"
                "  int y;\n"
                "  initial y = depth(3) * 100 + calls;\n"
                "endmodule\n",
                "y"),
      303u);
}

}  // namespace
