#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// Unit tests: ClassObject API
// ---------------------------------------------------------------------------

TEST(ClassAssignRenameSim, HandleAssignmentSharesObject) {
  SimFixture f;
  auto* type = MakeClassType(f, "Data", {"val"});
  auto [handle, obj] = MakeObj(f, type);
  obj->SetProperty("val", MakeLogic4VecVal(f.arena, 32, 10));

  auto* retrieved = f.ctx.GetClassObject(handle);
  EXPECT_EQ(retrieved, obj);
  EXPECT_EQ(retrieved->GetProperty("val", f.arena).ToUint64(), 10u);

  obj->SetProperty("val", MakeLogic4VecVal(f.arena, 32, 20));
  EXPECT_EQ(retrieved->GetProperty("val", f.arena).ToUint64(), 20u);
}

TEST(ClassAssignRenameSim, ShallowCopyCreatesNewObject) {
  SimFixture f;
  auto* type = MakeClassType(f, "Packet", {"data"});
  auto [h1, obj1] = MakeObj(f, type);
  obj1->SetProperty("data", MakeLogic4VecVal(f.arena, 32, 42));

  auto* copy = obj1->ShallowCopy(f.arena);
  ASSERT_NE(copy, nullptr);
  EXPECT_NE(copy, obj1);
  EXPECT_EQ(copy->type, obj1->type);
  EXPECT_EQ(copy->GetProperty("data", f.arena).ToUint64(), 42u);
}

TEST(ClassAssignRenameSim, ShallowCopyPropertiesIndependent) {
  SimFixture f;
  auto* type = MakeClassType(f, "C", {"x"});
  auto [h1, obj1] = MakeObj(f, type);
  obj1->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 10));

  auto* copy = obj1->ShallowCopy(f.arena);

  copy->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 99));
  EXPECT_EQ(obj1->GetProperty("x", f.arena).ToUint64(), 10u);
  EXPECT_EQ(copy->GetProperty("x", f.arena).ToUint64(), 99u);
}

TEST(ClassAssignRenameSim, ShallowCopyPreservesAllProperties) {
  SimFixture f;
  auto* type = MakeClassType(f, "Multi", {"a", "b", "c"});
  auto [h1, obj1] = MakeObj(f, type);
  obj1->SetProperty("a", MakeLogic4VecVal(f.arena, 32, 1));
  obj1->SetProperty("b", MakeLogic4VecVal(f.arena, 32, 2));
  obj1->SetProperty("c", MakeLogic4VecVal(f.arena, 32, 3));

  auto* copy = obj1->ShallowCopy(f.arena);
  EXPECT_EQ(copy->GetProperty("a", f.arena).ToUint64(), 1u);
  EXPECT_EQ(copy->GetProperty("b", f.arena).ToUint64(), 2u);
  EXPECT_EQ(copy->GetProperty("c", f.arena).ToUint64(), 3u);
}

TEST(ClassAssignRenameSim, ShallowCopySharesNestedHandles) {
  SimFixture f;
  auto* inner_type = MakeClassType(f, "Inner", {"val"});
  auto [inner_handle, inner_obj] = MakeObj(f, inner_type);
  inner_obj->SetProperty("val", MakeLogic4VecVal(f.arena, 32, 77));

  auto* outer_type = MakeClassType(f, "Outer", {"ref"});
  auto [outer_handle, outer_obj] = MakeObj(f, outer_type);

  outer_obj->SetProperty("ref", MakeLogic4VecVal(f.arena, 64, inner_handle));

  auto* copy = outer_obj->ShallowCopy(f.arena);

  EXPECT_EQ(copy->GetProperty("ref", f.arena).ToUint64(), inner_handle);
}

TEST(ClassAssignRenameSim, ShallowCopyPreservesDerivedType) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"j"});
  auto* ext = MakeClassType(f, "Ext", {"x"});
  ext->parent = base;

  auto [h, obj] = MakeObj(f, ext);
  obj->SetProperty("j", MakeLogic4VecVal(f.arena, 32, 5));
  obj->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 9));

  auto* copy = obj->ShallowCopy(f.arena);
  EXPECT_EQ(copy->type, ext);
  EXPECT_EQ(copy->GetProperty("j", f.arena).ToUint64(), 5u);
  EXPECT_EQ(copy->GetProperty("x", f.arena).ToUint64(), 9u);
}

// ---------------------------------------------------------------------------
// End-to-end tests: full pipeline (parse -> elaborate -> lower -> run)
// ---------------------------------------------------------------------------

TEST(ClassAssignRenameSim, E2eHandleAssignmentAliasesObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    p1.x = 10;\n"
      "    p2 = p1;\n"
      "    p2.x = 42;\n"
      "    result = p1.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 42u}});
}

TEST(ClassAssignRenameSim, E2eShallowCopyCopiesProperties) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    p1.x = 42;\n"
      "    p2 = new p1;\n"
      "    result = p2.x;\n"
      "  end\n"
      "endmodule\n", "result"), 42u);
}

TEST(ClassAssignRenameSim, E2eShallowCopyCreatesIndependentObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    p1.x = 10;\n"
      "    p2 = new p1;\n"
      "    p2.x = 99;\n"
      "    r1 = p1.x;\n"
      "    r2 = p2.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 10u}, {"r2", 99u}});
}

TEST(ClassAssignRenameSim, E2eShallowCopyDoesNotCallConstructor) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  function new();\n"
      "    x = 999;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    p1.x = 42;\n"
      "    p2 = new p1;\n"
      "    result = p2.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 42u}});
}

TEST(ClassAssignRenameSim, E2eShallowCopySharesNestedHandle) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Inner;\n"
      "  int val;\n"
      "endclass\n"
      "class Outer;\n"
      "  int x;\n"
      "  Inner a;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    Outer o1, o2;\n"
      "    o1 = new;\n"
      "    o1.a = new;\n"
      "    o1.a.val = 77;\n"
      "    o2 = new o1;\n"
      "    r1 = o2.a.val;\n"
      "    o2.a.val = 88;\n"
      "    r2 = o1.a.val;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 77u}, {"r2", 88u}});
}

TEST(ClassAssignRenameSim, E2eChainedMemberAccess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class A;\n"
      "  int j;\n"
      "endclass\n"
      "class B;\n"
      "  int i;\n"
      "  A a;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    B b1;\n"
      "    b1 = new;\n"
      "    b1.i = 1;\n"
      "    b1.a = new;\n"
      "    b1.a.j = 50;\n"
      "    r1 = b1.i;\n"
      "    r2 = b1.a.j;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 1u}, {"r2", 50u}});
}

TEST(ClassAssignRenameSim, E2eShallowCopyWithInheritance) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base;\n"
      "  int j;\n"
      "endclass\n"
      "class Ext extends Base;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    Ext e;\n"
      "    Base b;\n"
      "    e = new;\n"
      "    e.j = 5;\n"
      "    e.x = 9;\n"
      "    b = e;\n"
      "    Base b2;\n"
      "    b2 = new b;\n"
      "    r1 = b2.j;\n"
      "    r2 = b.j;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 5u}, {"r2", 5u}});
}

TEST(ClassAssignRenameSim, E2eShallowCopyMultipleProperties) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int a;\n"
      "  int b;\n"
      "  int c;\n"
      "endclass\n"
      "module t;\n"
      "  int ra, rb, rc;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    p1.a = 1;\n"
      "    p1.b = 2;\n"
      "    p1.c = 3;\n"
      "    p2 = new p1;\n"
      "    ra = p2.a;\n"
      "    rb = p2.b;\n"
      "    rc = p2.c;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"ra", 1u}, {"rb", 2u}, {"rc", 3u}});
}

}  // namespace
