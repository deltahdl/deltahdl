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
  EXPECT_EQ(RunAndGet(
      "class Demo;\n"
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
      "endmodule\n", "result"), 42u);
}

TEST(ClassSim, ThisPropertyReadInMethod) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
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
      "endmodule\n", "result"), 55u);
}

TEST(ClassSim, ThisPropertyWriteInMethod) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
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
      "endmodule\n", "result"), 77u);
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

}  // namespace
