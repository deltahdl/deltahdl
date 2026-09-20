#include <gtest/gtest.h>

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

}  // namespace
