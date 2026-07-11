#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

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

TEST(ClassSim, GetReachabilityWeaklyReachableViaWeakReference) {
  // §8.29 defines an object as weakly reachable when it is not strongly
  // reachable yet can still be reached by traversing a weak reference (the
  // construct introduced in §8.30). The classifier shares the same weak
  // reference registry the weak_reference methods rely on, so dropping the
  // lone strong handle while a weak reference survives leaves the object in
  // the weakly reachable level rather than unreachable.
  SimFixture f;
  auto* type = MakeClassType(f, "WeaklyHeld", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr;
  wr.referent_handle = handle;
  f.ctx.RegisterWeakReference(&wr);

  f.ctx.ReleaseObject(handle);
  EXPECT_EQ(f.ctx.GetReachability(handle), Reachability::kWeaklyReachable);
}

TEST(ClassSim, StrongReferenceDominatesWeakReference) {
  // §8.29 qualifies the weakly reachable level as applying only when an object
  // is *not* strongly reachable. An object that still owns a live strong handle
  // stays strongly reachable even while a weak reference also points at it, so
  // the strong classification must win over a coexisting weak reference.
  SimFixture f;
  auto* type = MakeClassType(f, "BothHeld", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr;
  wr.referent_handle = handle;
  f.ctx.RegisterWeakReference(&wr);

  // The creation reference count is still 1, so a strong reference coexists
  // with the weak one.
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

TEST(ClassSim, CollectGarbagePreservesObjectPinnedByActiveThis) {
  // §8.29 states that a newly created object is strongly reachable by the
  // process that created it. The simulator models the receiver of the
  // currently executing method with the `this` stack; the collector must treat
  // an object on that stack as live even when no named handle references it
  // yet. Collection runs only between processes in this build (never while a
  // method is mid-execution), so the active-`this` pinning is the one strong
  // reachability condition that cannot be reached from source and is exercised
  // directly here.
  SimFixture f;
  auto* type = MakeClassType(f, "Receiver", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  // Nothing in any variable scope roots the object; only the active `this`
  // keeps it reachable.
  f.ctx.PushThis(obj);
  f.ctx.CollectGarbage();
  EXPECT_NE(f.ctx.GetClassObject(handle), nullptr);

  // After the method returns and the receiver leaves the `this` stack, the now
  // unreferenced object becomes eligible for reclamation.
  f.ctx.PopThis();
  f.ctx.CollectGarbage();
  EXPECT_EQ(f.ctx.GetClassObject(handle), nullptr);
}

TEST(ClassSim, CollectGarbageReclaimsWeaklyReachableObject) {
  // §8.29: a weak reference never keeps an object alive. Once the last strong
  // handle is dropped the object is only weakly reachable, and garbage
  // collection may then carry its state to unreachable and reclaim the memory.
  SimFixture f;
  auto* type = MakeClassType(f, "WeakOnly", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr;
  wr.referent_handle = handle;
  f.ctx.RegisterWeakReference(&wr);

  f.ctx.ReleaseObject(handle);
  ASSERT_EQ(f.ctx.GetReachability(handle), Reachability::kWeaklyReachable);

  f.ctx.CollectGarbage();
  EXPECT_EQ(f.ctx.GetClassObject(handle), nullptr);
  EXPECT_EQ(f.ctx.GetReachability(handle), Reachability::kUnreachable);
}

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
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C p;\n"
                      "    p = new;\n"
                      "    result = (p != null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
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

// --- §8.29 sole normative shall, observed through the full pipeline ---------
//
// The synthetic CollectGarbage tests above hand-build objects with MakeObj and
// call the collector directly. §8.29's rule that "the system shall reclaim any
// object no longer being used" depends on how the object is produced (a real
// `new`, §8.4) and how it stops being used (a null assignment / leaving scope),
// so the tests below build the object from source, run the design, and only
// then observe the production collector applying strong-reachability to a live
// heap. Root discovery relies on the lowerer registering class-handle variables
// (lowerer_var.cpp), so no reachability metadata is stubbed here.

namespace {
// Counts objects still resident in the heap whose handle differs from `keep`.
// Handles are allocated monotonically from 1, so a small window covers every
// object a compact source program can create.
int ResidentOthers(SimFixture& f, uint64_t keep) {
  int n = 0;
  for (uint64_t h = 1; h <= keep + 8; ++h) {
    if (h != keep && f.ctx.GetClassObject(h) != nullptr) ++n;
  }
  return n;
}
}  // namespace

// C1: an object whose only handle is dropped at run time (`dead = null`) is
// reclaimed by the collector, while an object still referenced by a live
// module variable survives. Both objects are built by real `new`.
TEST(ClassSim, E2eGcReclaimsRuntimeDroppedObjectKeepsReferenced) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  C keep;\n"
      "  initial begin\n"
      "    C dead;\n"
      "    dead = new;\n"
      "    dead.x = 1;\n"
      "    keep = new;\n"
      "    keep.x = 2;\n"
      "    dead = null;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();

  auto* keep_var = f.ctx.FindVariable("keep");
  ASSERT_NE(keep_var, nullptr);
  uint64_t kept = keep_var->value.ToUint64();
  ASSERT_NE(kept, kNullClassHandle);
  ASSERT_NE(f.ctx.GetClassObject(kept), nullptr);

  // Before collection the dropped object is still resident (nothing eagerly
  // frees it); it is simply no longer rooted.
  EXPECT_EQ(ResidentOthers(f, kept), 1);

  f.ctx.CollectGarbage();

  // The referenced object survives; the unused one is reclaimed.
  EXPECT_NE(f.ctx.GetClassObject(kept), nullptr);
  EXPECT_EQ(ResidentOthers(f, kept), 0);
}

// C2 (strong-reachability closure): an inner object reachable only through a
// rooted outer object's non-static member is preserved by the collector, then
// reclaimed once the outer root is dropped.
TEST(ClassSim, E2eGcFollowsObjectReferenceChain) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Inner;\n"
      "  int v;\n"
      "endclass\n"
      "class Outer;\n"
      "  Inner inner;\n"
      "endclass\n"
      "module t;\n"
      "  Outer o;\n"
      "  initial begin\n"
      "    o = new;\n"
      "    o.inner = new;\n"
      "    o.inner.v = 9;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();

  auto* o_var = f.ctx.FindVariable("o");
  ASSERT_NE(o_var, nullptr);
  uint64_t outer_h = o_var->value.ToUint64();
  ASSERT_NE(outer_h, kNullClassHandle);
  auto* outer_obj = f.ctx.GetClassObject(outer_h);
  ASSERT_NE(outer_obj, nullptr);
  uint64_t inner_h = outer_obj->GetProperty("inner", f.arena).ToUint64();
  ASSERT_NE(inner_h, kNullClassHandle);
  ASSERT_NE(f.ctx.GetClassObject(inner_h), nullptr);

  // Outer is rooted by module variable `o`; the collector keeps both it and
  // the inner object reached only through outer's `inner` member.
  f.ctx.CollectGarbage();
  EXPECT_NE(f.ctx.GetClassObject(outer_h), nullptr);
  EXPECT_NE(f.ctx.GetClassObject(inner_h), nullptr);
}

// C1 transitive: dropping the outer root leaves the whole chain unreachable, so
// the collector reclaims both the outer object and its formerly-referenced
// inner object.
TEST(ClassSim, E2eGcReclaimsWholeUnreachableChain) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Inner;\n"
      "  int v;\n"
      "endclass\n"
      "class Outer;\n"
      "  Inner inner;\n"
      "endclass\n"
      "module t;\n"
      "  Outer o;\n"
      "  initial begin\n"
      "    o = new;\n"
      "    o.inner = new;\n"
      "    o = null;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();

  ASSERT_EQ(f.ctx.FindVariable("o")->value.ToUint64(), kNullClassHandle);
  // Two objects were created and neither is rooted after `o = null`.
  EXPECT_EQ(ResidentOthers(f, kNullClassHandle), 2);

  f.ctx.CollectGarbage();
  EXPECT_EQ(ResidentOthers(f, kNullClassHandle), 0);
}

// C1 input form: an object stops being used when its sole handle is reassigned
// to a fresh `new` (distinct from the null-assignment drop above). The
// superseded object is no longer reachable and is reclaimed, while the object
// the module variable now names survives. Both objects are built by real `new`.
TEST(ClassSim, E2eGcReclaimsObjectDroppedByReassignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  C p;\n"
      "  initial begin\n"
      "    p = new;\n"
      "    p.x = 1;\n"
      "    p = new;\n"
      "    p.x = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();

  auto* p_var = f.ctx.FindVariable("p");
  ASSERT_NE(p_var, nullptr);
  uint64_t current = p_var->value.ToUint64();
  ASSERT_NE(current, kNullClassHandle);

  // The object created by the first `new` is still resident but unrooted.
  EXPECT_EQ(ResidentOthers(f, current), 1);

  f.ctx.CollectGarbage();

  // The current object survives; the superseded one is reclaimed.
  EXPECT_NE(f.ctx.GetClassObject(current), nullptr);
  EXPECT_EQ(f.ctx.GetClassObject(current)->GetProperty("x", f.arena).ToUint64(),
            2u);
  EXPECT_EQ(ResidentOthers(f, current), 0);
}

}  // namespace
