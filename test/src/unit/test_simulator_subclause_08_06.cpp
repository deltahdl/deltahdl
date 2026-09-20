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

// §8.6: the lifetime of a class method shall be automatic. A method's local
// variable therefore gets fresh storage on every call and does not carry a
// value over from one invocation to the next. Each call to step() reads its
// local as its default and returns 1; a static lifetime would instead
// accumulate (1, 2, 3), so all-ones discriminates the required automatic
// lifetime being applied at run time.
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

// §8.6: the automatic-lifetime rule applies to class tasks as well as
// functions. A task local variable is re-created per call and does not persist,
// so repeated calls each observe the fresh default (a static lifetime would
// instead accumulate 1, 2, 3).
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

// §8.6 with §23.9: a bare name inside a method resolves against the class
// scope before the scope enclosing the class, so `sum = 5` and the loop
// variable `i` of a method write the object's properties even when the
// instantiating module declares variables of the same names; the module's
// stay 0. Before the fix the method wrote the module's `sum` and `i` and the
// properties stayed 0 -- the result reads h.sum * 1000 + h.i * 100 + t.sum
// * 10 + t.i, 5300 rather than 53.
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

// §8.6 with §23.9, the read side and the local that shadows both: a method
// reading its bare `tag` reads the property (7), not the module's `tag` (9),
// and a method declaring its own `tag` local reads that (4) before either.
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

// §8.4 and §8.6 with §24.3: a program is a scope that admits a data
// declaration, so `Cnt c = new(20)` as a program item holds an ordinary
// object and `c.inc()` in the program's initial runs on it. The object is
// created under the instance's name, `pr.c`, while the initial names it `c`;
// the declared class was on file under the instance's name alone, so the
// call found no class for `c`, ran nothing and answered 0 -- the result read
// 20 (the constructor's value, which the bare property read reached) rather
// than 2121, the 21 the call returns beside the 21 it left in the property.
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

// §8.4 and §8.6 with §27.4: each instance of a loop generate block declares
// its own `Cnt c = new(5)`, created under the block's name, `blk[0].c` and
// `blk[1].c`, and the initial of each block names its own as `c`. Block 1
// increments its object before both blocks read theirs at #1, so the result
// packs 5 from block 0 and 6 from block 1 as 605: the call ran on no object
// and answered 0 for both, and one object shared by the two blocks would
// read 606.
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

// §8.4 and §8.6 with §25.3: an interface item may be a class variable, and
// §8.5 reaches its property through the instance path, `i.c.v` from the
// module. The interface's own initial calls `c.inc()` on the object created
// as `i.c` and keeps the 13 it returns in `i.r`; the module then reads `i.r`
// and `i.c.v` at #1, 1313. The call answered 0 as the program's did, and the
// property read split `i.c.v` at its first dot, `i` -- an instance, not a
// variable -- against `c.v`, and read 0 where the split at `i.c` reads 13.
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

// §8.6 (printed page 183) calls an object's method through its handle, §13.3
// (printed 337) declares a method's formal with any data_type, and §7.2.1
// (printed 147) lays an inline union out member by member, `pair_t Add`
// naming a typedef of a structure the module declares. A class's methods
// are reached by no item walk, so the elaborator resolved a formal's
// typedef-named members for the module's own subroutines alone: C's f was
// sized as if Add were a scalar, its layout gave Add no members to place
// `'{3, 4}` by or to read `a.Add.a` through, and `h.f(tagged Add '{3, 4})`
// answered 0 where §10.9.2 (printed 263) places 3 into a and 4 into b, 34.
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

// §26.2 (printed page 808) with §8.6 (printed 183): a package's class sees
// the package's typedefs, and its method is called through a handle a
// module's procedure declares after `import p::*;`. The package's classes
// were reached by no item walk either, so `q.sum(tagged Pt '{5, 6})` read 0
// from the same shape of body where §7.2.1 places 5 and 6, 56.
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
                      "    Geo q = new;\n"
                      "    r = q.sum(tagged Pt '{5, 6});\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            56u);
}

// §3.12.1 with §8.23 (printed page 200): a class declared outside every
// design element stands in the compilation-unit scope, and a typedef the
// class's own body declares stands by its bare name inside the class, so the
// member `duo_t Two` names the class's typedef, which the unit's table does
// not hold: a resolution reading that table alone would find no duo_t.
// `k.m(tagged Two '{7, 8})` reads 78 where the unresolved member read 0.
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

// §6.18 (printed page 118) has a user-defined type's declaration precede
// every reference to its name, and lets a forward typedef stand for a
// definition the same scope gives before or after the reference, so a
// class written between `typedef struct pair_t;` and the structure's
// definition names pair_t lawfully in a method's formal, which §23.9
// (printed 761) resolves outward from the class to the module's typedef.
// The class's methods were resolved against the typedefs as they stood at
// the class, where the forward name held a placeholder with no members, so
// C's f was sized as if A were a scalar and `h.f(tagged A '{3, 4})` read 0
// where §7.2.1 places 3 into a and 4 into b, 34.
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

// §8.6 (printed page 183 of the LRM): an object's methods are accessed by
// qualifying the method name with a handle to the object, and §7.4.2
// (printed 153-154) and §7.10 (printed 169) make each element of an array or
// a queue declared with a class's name such a handle. The three tests below
// share the class and read its get() -- 7, the property's initializer -- or
// the property run() wrote; a call that reached no method ran nothing and
// read 0. Before this only an associative array's element had a dispatch
// (TryEvalAssocElementMethodCall in eval_assoc_class_handles.cpp).
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

// A queue's element, pushed as a handle and called through `q[0]`.
TEST(ObjectMethodSim, MethodCalledThroughAQueueElementRuns) {
  EXPECT_EQ(RunAndGet(ElementMethodDesign("module t;\n"
                                          "  C q[$];\n"
                                          "  int y;\n"
                                          "  initial begin\n"
                                          "    C c = new;\n"
                                          "    q.push_back(c);\n"
                                          "    y = q[0].get();\n"
                                          "  end\n"
                                          "endmodule\n"),
                      "y"),
            7u);
}

// A task enabled through the element as a statement: run() adds one to the
// object's v, which get() then reads as 8.
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

// §8.6 (printed page 183): a method is accessed through any handle to its
// object, and a property of a class type is one (§8.4), so `h.kid.get()`
// runs get() on the C that H's `kid` holds, and `arr[0].kid.get()` on the
// one an element's object holds. The method-call evaluator's receivers were
// a variable, `p::h`, a call's result and a container's element
// (TryDispatchMethodOrLet in eval_function.cpp), so a chained property
// receiver reached no arm and the call read 0.
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

// A call's result as the receiver, `h.get_kid().get()`, which
// TryEvalCallResultMethodCall (eval_call_result.cpp) served already; pinned
// beside the chained property so the two receivers stay served by one arm
// each and neither evaluates the call twice.
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

}  // namespace
