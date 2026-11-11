#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ClassSim, ThisPushPop) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_EQ(f.ctx.CurrentThis(), nullptr);
  f.ctx.PushThis(obj);
  EXPECT_EQ(f.ctx.CurrentThis(), obj);
  f.ctx.PopThis();
  EXPECT_EQ(f.ctx.CurrentThis(), nullptr);
}

TEST(ClassSim, NestedThisScoping) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {"x"});
  auto [h1, obj1] = MakeObj(f, type);
  auto [h2, obj2] = MakeObj(f, type);

  f.ctx.PushThis(obj1);
  EXPECT_EQ(f.ctx.CurrentThis(), obj1);
  f.ctx.PushThis(obj2);
  EXPECT_EQ(f.ctx.CurrentThis(), obj2);
  f.ctx.PopThis();
  EXPECT_EQ(f.ctx.CurrentThis(), obj1);
  f.ctx.PopThis();
  EXPECT_EQ(f.ctx.CurrentThis(), nullptr);
}

TEST(ClassSim, ThisPropertyAccess) {
  SimFixture f;
  auto* type = MakeClassType(f, "Demo", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  obj->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 99));
  f.ctx.PushThis(obj);

  auto* current = f.ctx.CurrentThis();
  ASSERT_NE(current, nullptr);
  auto val = current->GetProperty("x", f.arena);
  EXPECT_EQ(val.ToUint64(), 99u);

  f.ctx.PopThis();
}

TEST(ClassSim, ThisCorrectObjectInNestedCalls) {
  SimFixture f;
  auto* type = MakeClassType(f, "C", {"val"});
  auto [h1, obj1] = MakeObj(f, type);
  auto [h2, obj2] = MakeObj(f, type);

  obj1->SetProperty("val", MakeLogic4VecVal(f.arena, 32, 10));
  obj2->SetProperty("val", MakeLogic4VecVal(f.arena, 32, 20));

  f.ctx.PushThis(obj1);
  EXPECT_EQ(f.ctx.CurrentThis()->GetProperty("val", f.arena).ToUint64(), 10u);

  f.ctx.PushThis(obj2);
  EXPECT_EQ(f.ctx.CurrentThis()->GetProperty("val", f.arena).ToUint64(), 20u);

  f.ctx.PopThis();
  EXPECT_EQ(f.ctx.CurrentThis()->GetProperty("val", f.arena).ToUint64(), 10u);

  f.ctx.PopThis();
}

TEST(ClassSim, PopThisOnEmptyStackIsSafe) {
  SimFixture f;
  EXPECT_EQ(f.ctx.CurrentThis(), nullptr);
  f.ctx.PopThis();
  EXPECT_EQ(f.ctx.CurrentThis(), nullptr);
}

TEST(ClassSim, ThisDisambiguatesPropertyFromArg) {
  EXPECT_EQ(RunAndGet("class Demo;\n"
                      "  integer x;\n"
                      "  function new(integer x);\n"
                      "    this.x = x;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Demo d;\n"
                      "    d = new(42);\n"
                      "    result = d.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(ClassSim, ThisPropertyReadInMethod) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int data;\n"
                      "  function int get_data();\n"
                      "    return this.data;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    c.data = 55;\n"
                      "    result = c.get_data();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            55u);
}

TEST(ClassSim, ThisPropertyWriteInMethod) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int data;\n"
                      "  function void set_data(int data);\n"
                      "    this.data = data;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    c.set_data(77);\n"
                      "    result = c.data;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            77u);
}

TEST(ClassSim, ThisTwoObjectsIndependent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int val;\n"
      "  function void set_val(int val);\n"
      "    this.val = val;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    C a, b;\n"
      "    a = new;\n"
      "    b = new;\n"
      "    a.set_val(10);\n"
      "    b.set_val(20);\n"
      "    r1 = a.val;\n"
      "    r2 = b.val;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 10u}, {"r2", 20u}});
}

TEST(ClassSim, ThisMultipleProperties) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int a;\n"
      "  int b;\n"
      "  function new(int a, int b);\n"
      "    this.a = a;\n"
      "    this.b = b;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ra, rb;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new(3, 7);\n"
      "    ra = c.a;\n"
      "    rb = c.b;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"ra", 3u}, {"rb", 7u}});
}

TEST(ClassSim, UnqualifiedPropertyWriteInMethodWakesAnEventControlOnIt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    int f;\n"
      "    function void bump(); f = 1; endfunction\n"
      "  endclass\n"
      "  C obj = new();\n"
      "  int b;\n"
      "  always @(obj.f) b = obj.f;\n"
      "  initial begin\n"
      "    #1 obj.bump();\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ClassSim, ThisPropertyWriteInMethodWakesAnEventControlOnIt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    int f;\n"
      "    function void bump(); this.f = 1; endfunction\n"
      "  endclass\n"
      "  C obj = new();\n"
      "  int b;\n"
      "  always @(obj.f) b = obj.f;\n"
      "  initial begin\n"
      "    #1 obj.bump();\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ClassSim, SuperPropertyWriteInMethodWakesAnEventControlOnIt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class B;\n"
      "    int f;\n"
      "  endclass\n"
      "  class D extends B;\n"
      "    function void bump(); super.f = 1; endfunction\n"
      "  endclass\n"
      "  D obj = new();\n"
      "  int b;\n"
      "  always @(obj.f) b = obj.f;\n"
      "  initial begin\n"
      "    #1 obj.bump();\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ClassSim, HandlePropertyWriteWakesAnEventControlOnIt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    int f;\n"
      "  endclass\n"
      "  C obj = new();\n"
      "  int b;\n"
      "  always @(obj.f) b = obj.f;\n"
      "  initial begin\n"
      "    #1 obj.f = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ClassSim, PropertyWriteThroughOneHandleWakesAnAliasOfTheSameObject) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    int f;\n"
      "  endclass\n"
      "  C obj = new();\n"
      "  C q = obj;\n"
      "  int b;\n"
      "  always @(q.f) b = q.f;\n"
      "  initial begin\n"
      "    #1 obj.f = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ClassSim, TaskLocalHandleHidesTheSameNamedProperty) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class O;\n"
      "    int n = 7;\n"
      "    function int get(); return n; endfunction\n"
      "  endclass\n"
      "  class P;\n"
      "    O d;\n"
      "    task run(output int r);\n"
      "      O d;\n"
      "      d = new;\n"
      "      d.n = 3;\n"
      "      r = d.get() * 10 + (this.d == null);\n"
      "    endtask\n"
      "  endclass\n"
      "  int r;\n"
      "  initial begin\n"
      "    static P p = new;\n"
      "    p.run(r);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 31u);
}

TEST(ClassThisSim, ThisPathReadsAMemberOfAStructProperty) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef struct { int a; int b; } s_t;\n"
                 "  class C;\n"
                 "    s_t s;\n"
                 "    function void fill(); s.a = 17; s.b = 42; endfunction\n"
                 "    function int sum(); return this.s.a + this.s.b; "
                 "endfunction\n"
                 "  endclass\n"
                 "  C h;\n"
                 "  initial begin\n"
                 "    h = new; h.fill();\n"
                 "    $display(\"%0d %0d\", h.sum(), h.s.a);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "59 17\n");
}

TEST(ClassThisSim, AMemberOfAnElementOfAHandleArrayPropertyIsWrittenInAMethod) {
  SimFixture f;
  auto out = RunCapture(
      "class K;\n"
      "  int v;\n"
      "endclass\n"
      "class H;\n"
      "  K kids[2];\n"
      "  function void mk(); kids[0] = new; kids[1] = new; endfunction\n"
      "  function void setv(); kids[1].v = 7; kids[0].v = 2; endfunction\n"
      "  function void thisset(); this.kids[0].v = 5; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    automatic H h = new;\n"
      "    h.mk();\n"
      "    h.setv();\n"
      "    $display(\"%0d %0d\", h.kids[1].v, h.kids[0].v);\n"
      "    h.thisset();\n"
      "    $display(\"%0d %0d\", h.kids[1].v, h.kids[0].v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "7 2\n7 5\n");
}

TEST(ThisSim, ThisReachesTheParametersOfTheObjectsSpecialization) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C #(int P = 3);\n"
      "  localparam int L = P * 2;\n"
      "  parameter int B = 5;\n"
      "  rand int x;\n"
      "  int t;\n"
      "  constraint c { x == this.P; }\n"
      "  function int gp(); return this.P; endfunction\n"
      "  function int gl(); return this.L; endfunction\n"
      "  function int gb(); return this.B; endfunction\n"
      "  function int bare(); return P * 100 + L * 10 + B; endfunction\n"
      "  task tk(); t = this.P + this.L; endtask\n"
      "endclass\n"
      "class D extends C #(4);\n"
      "  function int dp(); return this.P * 10 + this.L; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C c3 = new;\n"
      "  C #(7) c7 = new;\n"
      "  D d = new;\n"
      "  int r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11;\n"
      "  initial begin\n"
      "    c3.tk(); c7.tk();\n"
      "    void'(c7.randomize());\n"
      "    r1 = c3.gp(); r2 = c7.gp(); r3 = c3.gl(); r4 = c7.gl();\n"
      "    r5 = c3.gb(); r6 = c3.bare(); r7 = c7.bare();\n"
      "    r8 = c3.t; r9 = c7.t; r10 = c7.x; r11 = d.dp();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 3u},
                    {"r2", 7u},
                    {"r3", 6u},
                    {"r4", 14u},
                    {"r5", 5u},
                    {"r6", 365u},
                    {"r7", 845u},
                    {"r8", 9u},
                    {"r9", 21u},
                    {"r10", 7u},
                    {"r11", 48u}});
}

TEST(ThisSim, ThisIsTheHandleOfTheObjectTheMethodWasCalledOn) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  typedef type(this) self_t;\n"
      "  int v;\n"
      "  function C self(); return this; endfunction\n"
      "  function bit same(C o); return o == this; endfunction\n"
      "  function self_t me(); self_t m; m = this; return m; endfunction\n"
      "endclass\n"
      "class Reg;\n"
      "  C items[$];\n"
      "  function void add(C c); items.push_back(c); endfunction\n"
      "endclass\n"
      "class K extends C;\n"
      "  function void join_reg(Reg g); g.add(this); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C a = new, b = new;\n"
      "  K k = new;\n"
      "  Reg g = new;\n"
      "  int r1, r2, r3, r4, r5, r6;\n"
      "  initial begin\n"
      "    k.join_reg(g);\n"
      "    k.v = 33;\n"
      "    r1 = a.self() == a; r2 = a.self() == b;\n"
      "    r3 = a.same(a); r4 = a.same(b);\n"
      "    r5 = g.items[0].v; r6 = a.me() == a;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 1u},
                    {"r2", 0u},
                    {"r3", 1u},
                    {"r4", 0u},
                    {"r5", 33u},
                    {"r6", 1u}});
}

TEST(ThisSim, DISABLED_ThisInAnInlineConstraintOfAMethodNamesTheObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  rand int r, q;\n"
      "  function void rnd(); void'(randomize() with { r == 5; }); "
      "endfunction\n"
      "  function void rnd2();\n"
      "    void'(this.randomize() with { this.q == 6; });\n"
      "  endfunction\n"
      "  function void rnd3();\n"
      "    int ok;\n"
      "    ok = randomize() with { this.r == 7; };\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C a = new, b = new, c = new;\n"
      "  int r1, r2, r3, r4;\n"
      "  initial begin\n"
      "    a.rnd(); b.rnd2(); c.rnd3();\n"
      "    r1 = a.r; r2 = b.q; r3 = c.r;\n"
      "    void'(a.randomize() with { q == 8; });\n"
      "    r4 = a.q;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 5u}, {"r2", 6u}, {"r3", 7u}, {"r4", 8u}});
}

}  // namespace
