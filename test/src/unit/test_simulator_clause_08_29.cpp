#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// Unit tests: ClassObject memory management API
// ---------------------------------------------------------------------------

TEST(ClassSim, MemMgmtPropertiesPersist) {
  SimFixture f;
  auto* type = MakeClassType(f, "Persistent", {"data"});
  auto [handle, obj] = MakeObj(f, type);
  obj->SetProperty("data", MakeLogic4VecVal(f.arena, 32, 42));
  auto* retrieved = f.ctx.GetClassObject(handle);
  ASSERT_NE(retrieved, nullptr);
  EXPECT_EQ(retrieved->GetProperty("data", f.arena).ToUint64(), 42u);
}

TEST(ClassSim, DeallocatedObjectBecomesInvalid) {
  SimFixture f;
  auto* type = MakeClassType(f, "Temp", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  ASSERT_NE(f.ctx.GetClassObject(handle), nullptr);

  f.ctx.DeallocateClassObject(handle);
  EXPECT_EQ(f.ctx.GetClassObject(handle), nullptr);
}

TEST(ClassSim, DeallocateNullHandleIsHarmless) {
  SimFixture f;
  f.ctx.DeallocateClassObject(kNullClassHandle);
  f.ctx.DeallocateClassObject(99999);
}

TEST(ClassSim, NewObjectIsStronglyReachable) {
  SimFixture f;
  auto* type = MakeClassType(f, "Fresh", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_NE(handle, kNullClassHandle);
  auto* retrieved = f.ctx.GetClassObject(handle);
  ASSERT_NE(retrieved, nullptr);
  EXPECT_EQ(retrieved, obj);
}

TEST(ClassSim, ObjectAccessibleThroughMultipleHandles) {
  SimFixture f;
  auto* type = MakeClassType(f, "Shared", {"data"});
  auto [handle, obj] = MakeObj(f, type);
  obj->SetProperty("data", MakeLogic4VecVal(f.arena, 32, 55));

  uint64_t handle_copy = handle;
  auto* via_original = f.ctx.GetClassObject(handle);
  auto* via_copy = f.ctx.GetClassObject(handle_copy);
  EXPECT_EQ(via_original, via_copy);
  EXPECT_EQ(via_copy->GetProperty("data", f.arena).ToUint64(), 55u);
}

TEST(ClassSim, IndependentObjectsIndependentLifetimes) {
  SimFixture f;
  auto* type = MakeClassType(f, "Item", {"v"});
  auto [h1, o1] = MakeObj(f, type);
  auto [h2, o2] = MakeObj(f, type);
  o1->SetProperty("v", MakeLogic4VecVal(f.arena, 32, 1));
  o2->SetProperty("v", MakeLogic4VecVal(f.arena, 32, 2));

  f.ctx.DeallocateClassObject(h1);
  EXPECT_EQ(f.ctx.GetClassObject(h1), nullptr);

  auto* still_alive = f.ctx.GetClassObject(h2);
  ASSERT_NE(still_alive, nullptr);
  EXPECT_EQ(still_alive->GetProperty("v", f.arena).ToUint64(), 2u);
}

TEST(ClassSim, HandleIdNotReusedAfterDeallocation) {
  SimFixture f;
  auto* type = MakeClassType(f, "Ephemeral", {"x"});
  auto [h1, o1] = MakeObj(f, type);
  f.ctx.DeallocateClassObject(h1);

  auto [h2, o2] = MakeObj(f, type);
  EXPECT_NE(h1, h2);
}

TEST(ClassSim, NewObjectRefCountIsOne) {
  SimFixture f;
  auto* type = MakeClassType(f, "Rc", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  EXPECT_EQ(obj->ref_count, 1u);
}

TEST(ClassSim, RetainIncrementsRefCount) {
  SimFixture f;
  auto* type = MakeClassType(f, "Rc", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  EXPECT_EQ(obj->ref_count, 1u);
  f.ctx.RetainObject(handle);
  EXPECT_EQ(obj->ref_count, 2u);
}

TEST(ClassSim, ReleaseDecrementsRefCount) {
  SimFixture f;
  auto* type = MakeClassType(f, "Rc", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  f.ctx.RetainObject(handle);
  EXPECT_EQ(obj->ref_count, 2u);
  f.ctx.ReleaseObject(handle);
  EXPECT_EQ(obj->ref_count, 1u);
}

TEST(ClassSim, RetainNullHandleIsHarmless) {
  SimFixture f;
  f.ctx.RetainObject(kNullClassHandle);
  f.ctx.RetainObject(99999);
}

TEST(ClassSim, ReleaseNullHandleIsHarmless) {
  SimFixture f;
  f.ctx.ReleaseObject(kNullClassHandle);
  f.ctx.ReleaseObject(99999);
}

TEST(ClassSim, ReleaseDoesNotUnderflow) {
  SimFixture f;
  auto* type = MakeClassType(f, "Rc", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  f.ctx.ReleaseObject(handle);
  EXPECT_EQ(obj->ref_count, 0u);
  f.ctx.ReleaseObject(handle);
  EXPECT_EQ(obj->ref_count, 0u);
}

TEST(ClassSim, GetReachabilityStronglyReachable) {
  SimFixture f;
  auto* type = MakeClassType(f, "Live", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  EXPECT_EQ(f.ctx.GetReachability(handle), Reachability::kStronglyReachable);
}

TEST(ClassSim, GetReachabilityUnreachableAfterRelease) {
  SimFixture f;
  auto* type = MakeClassType(f, "Dead", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  f.ctx.ReleaseObject(handle);
  EXPECT_EQ(f.ctx.GetReachability(handle), Reachability::kUnreachable);
}

TEST(ClassSim, GetReachabilityNullIsUnreachable) {
  SimFixture f;
  EXPECT_EQ(f.ctx.GetReachability(kNullClassHandle),
            Reachability::kUnreachable);
}

TEST(ClassSim, GetReachabilityInvalidHandleIsUnreachable) {
  SimFixture f;
  EXPECT_EQ(f.ctx.GetReachability(99999), Reachability::kUnreachable);
}

TEST(ClassSim, GetReachabilityDeallocatedIsUnreachable) {
  SimFixture f;
  auto* type = MakeClassType(f, "Gone", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  f.ctx.DeallocateClassObject(handle);
  EXPECT_EQ(f.ctx.GetReachability(handle), Reachability::kUnreachable);
}

TEST(ClassSim, CollectGarbageEmptyHeapIsHarmless) {
  SimFixture f;
  f.ctx.CollectGarbage();
}

TEST(ClassSim, CollectGarbageReclaimsUnreferencedObject) {
  SimFixture f;
  auto* type = MakeClassType(f, "Garbage", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  ASSERT_NE(f.ctx.GetClassObject(handle), nullptr);

  f.ctx.CollectGarbage();
  EXPECT_EQ(f.ctx.GetClassObject(handle), nullptr);
}

TEST(ClassSim, CollectGarbagePreservesReferencedObject) {
  SimFixture f;
  auto* type = MakeClassType(f, "Keeper", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  auto* var = f.ctx.CreateVariable("keeper", 64);
  f.ctx.SetVariableClassType("keeper", "Keeper");
  var->value = MakeLogic4VecVal(f.arena, 64, handle);

  f.ctx.CollectGarbage();
  EXPECT_NE(f.ctx.GetClassObject(handle), nullptr);
}

TEST(ClassSim, CollectGarbagePreservesTransitiveReference) {
  SimFixture f;
  auto* outer_type = MakeClassType(f, "Outer", {"inner_ref"});
  auto* inner_type = MakeClassType(f, "Inner", {"val"});

  auto [inner_h, inner_obj] = MakeObj(f, inner_type);
  auto [outer_h, outer_obj] = MakeObj(f, outer_type);
  outer_obj->SetProperty("inner_ref", MakeLogic4VecVal(f.arena, 64, inner_h));

  auto* var = f.ctx.CreateVariable("root", 64);
  f.ctx.SetVariableClassType("root", "Outer");
  var->value = MakeLogic4VecVal(f.arena, 64, outer_h);

  f.ctx.CollectGarbage();
  EXPECT_NE(f.ctx.GetClassObject(outer_h), nullptr);
  EXPECT_NE(f.ctx.GetClassObject(inner_h), nullptr);
}

TEST(ClassSim, CollectGarbageReclaimsTransitivelyUnreachable) {
  SimFixture f;
  auto* outer_type = MakeClassType(f, "Outer", {"inner_ref"});
  auto* inner_type = MakeClassType(f, "Inner", {"val"});

  auto [inner_h, inner_obj] = MakeObj(f, inner_type);
  auto [outer_h, outer_obj] = MakeObj(f, outer_type);
  outer_obj->SetProperty("inner_ref", MakeLogic4VecVal(f.arena, 64, inner_h));

  f.ctx.CollectGarbage();
  EXPECT_EQ(f.ctx.GetClassObject(outer_h), nullptr);
  EXPECT_EQ(f.ctx.GetClassObject(inner_h), nullptr);
}

TEST(ClassSim, CollectGarbagePreservesObjectWithPendingNba) {
  SimFixture f;
  auto* type = MakeClassType(f, "Nba", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  auto* var = f.ctx.CreateVariable("nba_var", 64);
  f.ctx.SetVariableClassType("nba_var", "Nba");
  var->value = MakeLogic4VecVal(f.arena, 64, kNullClassHandle);
  var->pending_nba = MakeLogic4VecVal(f.arena, 64, handle);
  var->has_pending_nba = true;

  f.ctx.CollectGarbage();
  EXPECT_NE(f.ctx.GetClassObject(handle), nullptr);
}

// ---------------------------------------------------------------------------
// End-to-end tests: full pipeline (parse -> elaborate -> lower -> run)
// ---------------------------------------------------------------------------

TEST(ClassSim, E2eNullAssignmentReleasesReference) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C p;\n"
      "    p = new;\n"
      "    p.x = 10;\n"
      "    p = null;\n"
      "    result = (p == null);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 1u}});
}

TEST(ClassSim, E2eObjectPersistsThroughHandleCopy) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C a, b;\n"
      "    a = new;\n"
      "    a.x = 77;\n"
      "    b = a;\n"
      "    a = null;\n"
      "    result = b.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 77u}});
}

TEST(ClassSim, E2eMultipleObjectsIndependent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    C a, b;\n"
      "    a = new;\n"
      "    b = new;\n"
      "    a.x = 10;\n"
      "    b.x = 20;\n"
      "    r1 = a.x;\n"
      "    r2 = b.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 10u}, {"r2", 20u}});
}

TEST(ClassSim, E2eNewObjectDefaultsToNonNull) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C p;\n"
      "    p = new;\n"
      "    result = (p != null);\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

TEST(ClassSim, E2eReassignToNewObjectOldHandleLost) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C p;\n"
      "    p = new;\n"
      "    p.x = 10;\n"
      "    p = new;\n"
      "    result = p.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 0u}});
}

}  // namespace
