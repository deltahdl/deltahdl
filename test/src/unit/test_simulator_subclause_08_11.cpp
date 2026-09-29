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

// §9.4.2: a change to a data member of an object, to an element of an
// aggregate or to the size of a dynamic array, read through a method or a
// function, reevaluates the event expression. A class handle's own
// bits never move, so the announcement is the whole of what a process reading
// `obj.f` has to go on, and the clause draws no distinction between the
// spellings the four cases below use. The reader is an event control on the
// property, `@(obj.f)`: an always_comb reading `obj.f` is no reader here,
// since §9.2.2.2.1 keeps references to class objects out of its sensitivity.
// This one writes the property by its bare name inside a method.
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

// §8.11's `this.f`, a different write site from the bare name above.
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

// §8.15's `super.f`, which writes the parent slice through a third site again.
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

// The guard: the write spelled through the handle, which announced itself all
// along. It pins the arm that worked, so the three above cannot be paid for by
// moving the notification off it.
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

// The set the announcement answers is the variables designating the object, not
// the one the statement named: §8.12 leaves `q` and `obj` denoting one object,
// so a write through either is a change the other is watching.
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

// §8.11 (printed page 187): an unqualified name in a method resolves in the
// innermost scope, so a task's own `O d;` hides the property d, which `this.d`
// alone reaches. The local, a class handle, was declared design-wide rather
// than in the task's frame, so `d = new` and `d.n = 3` went to the property
// while `d.get()` called through the null design-wide d.
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

// §8.11 with §7.2: `this.s` is the property s of the object the method runs on,
// so `this.s.a` reads the member the bare `s.a` wrote, 17, as `h.s.a` does
// from outside.
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

}  // namespace
