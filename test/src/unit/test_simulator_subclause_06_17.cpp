#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §6.17: lowering a bare `event` declaration materializes an event handle.
TEST(Lowerer, EventVariableCreated) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("ev");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->is_event);
}

// §6.17 para 2: an event variable has a persistent triggered state that lasts
// for the whole time step. (The trigger/wait mechanism itself is §9.4.2/§15.5.)
TEST(Simulator, EventTriggeredStatePersistsInTimestep) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  initial ->ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_FALSE(f.ctx.IsEventTriggered("ev"));

  f.ctx.SetEventTriggered("ev");
  EXPECT_TRUE(f.ctx.IsEventTriggered("ev"));
}

// §6.17 para 4: with no initializer, each event is bound to its own new
// synchronization object -> distinct handles, none of them null.
TEST(Simulator, EventDefaultInitYieldsDistinctSyncObjects) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a;\n"
      "  event b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_NE(va, vb);
  EXPECT_FALSE(va->is_null_event);
  EXPECT_FALSE(vb->is_null_event);
}

// §6.17 para 3: `event empty = null;` declares an event with no synchronization
// object (the null-initializer form, driven from real source).
TEST(Simulator, EventInitializedWithNullFlag) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev = null;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("ev");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->is_null_event);
}

// §6.17 para 3: `event done_too = done;` aliases `done_too` to `done`, so both
// names refer to the same synchronization object (the alias-initializer form).
TEST(Simulator, EventAliasInitializerSharesSyncObject) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event done;\n"
      "  event done_too = done;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* done = f.ctx.FindVariable("done");
  auto* done_too = f.ctx.FindVariable("done_too");
  ASSERT_NE(done, nullptr);
  ASSERT_NE(done_too, nullptr);
  EXPECT_EQ(done, done_too);
}

// §6.17 para 3: a procedural assignment `b = a` between event variables makes
// both refer to the same synchronization object. Observed end-to-end: before
// the assignment `a == b` is false (distinct default objects); after it is
// true (shared object). Also exercises the event `==` comparison rule.
TEST(Simulator, EventProceduralAssignAliasesObservedByEquality) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a;\n"
      "  event b;\n"
      "  bit before_eq;\n"
      "  bit after_eq;\n"
      "  initial begin\n"
      "    before_eq = (a == b);\n"
      "    b = a;\n"
      "    after_eq = (a == b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* before_eq = f.ctx.FindVariable("before_eq");
  auto* after_eq = f.ctx.FindVariable("after_eq");
  ASSERT_NE(before_eq, nullptr);
  ASSERT_NE(after_eq, nullptr);
  EXPECT_EQ(before_eq->value.ToUint64(), 0u);
  EXPECT_EQ(after_eq->value.ToUint64(), 1u);
}

// §6.17 para 3: the same aliasing rule observed through the event `!=`
// comparison. Distinct default objects are unequal (before), the shared object
// is not unequal (after).
TEST(Simulator, EventProceduralAssignAliasesObservedByInequality) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a;\n"
      "  event b;\n"
      "  bit before_ne;\n"
      "  bit after_ne;\n"
      "  initial begin\n"
      "    before_ne = (a != b);\n"
      "    b = a;\n"
      "    after_ne = (a != b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* before_ne = f.ctx.FindVariable("before_ne");
  auto* after_ne = f.ctx.FindVariable("after_ne");
  ASSERT_NE(before_ne, nullptr);
  ASSERT_NE(after_ne, nullptr);
  EXPECT_EQ(before_ne->value.ToUint64(), 1u);
  EXPECT_EQ(after_ne->value.ToUint64(), 0u);
}

// §6.17 para 3: assigning `null` to an event variable breaks the association
// with its synchronization object. Observed end-to-end via `ev == null`: false
// while bound, true after nullification. Also exercises event-vs-null compare.
TEST(Simulator, EventAssignNullBreaksAssociationObservedByNullCompare) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  bit before_null;\n"
      "  bit after_null;\n"
      "  initial begin\n"
      "    before_null = (ev == null);\n"
      "    ev = null;\n"
      "    after_null = (ev == null);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* before_null = f.ctx.FindVariable("before_null");
  auto* after_null = f.ctx.FindVariable("after_null");
  ASSERT_NE(before_null, nullptr);
  ASSERT_NE(after_null, nullptr);
  EXPECT_EQ(before_null->value.ToUint64(), 0u);
  EXPECT_EQ(after_null->value.ToUint64(), 1u);
}

// §6.17 para 3: comparison against `null` is symmetric in operand order, so a
// `null == ev` comparison (null on the left) tracks the event's association the
// same way `ev == null` does: false while bound, true once nullified. Observed
// end-to-end, exercising the null-on-left comparison path.
TEST(Simulator, EventNullOnLeftComparesAgainstAssociation) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  bit bound_cmp;\n"
      "  bit null_cmp;\n"
      "  initial begin\n"
      "    bound_cmp = (null == ev);\n"
      "    ev = null;\n"
      "    null_cmp = (null == ev);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* bound_cmp = f.ctx.FindVariable("bound_cmp");
  auto* null_cmp = f.ctx.FindVariable("null_cmp");
  ASSERT_NE(bound_cmp, nullptr);
  ASSERT_NE(null_cmp, nullptr);
  EXPECT_EQ(bound_cmp->value.ToUint64(), 0u);
  EXPECT_EQ(null_cmp->value.ToUint64(), 1u);
}

// §6.17 para 3: an event variable can also be compared to `null` with `!=`. A
// bound event differs from null (true); after its association is broken it no
// longer differs (false). Observed end-to-end, exercising the inequality path
// of the event-vs-null comparison.
TEST(Simulator, EventNotEqualNullTracksAssociation) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  bit bound_ne;\n"
      "  bit null_ne;\n"
      "  initial begin\n"
      "    bound_ne = (ev != null);\n"
      "    ev = null;\n"
      "    null_ne = (ev != null);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* bound_ne = f.ctx.FindVariable("bound_ne");
  auto* null_ne = f.ctx.FindVariable("null_ne");
  ASSERT_NE(bound_ne, nullptr);
  ASSERT_NE(null_ne, nullptr);
  EXPECT_EQ(bound_ne->value.ToUint64(), 1u);
  EXPECT_EQ(null_ne->value.ToUint64(), 0u);
}

// §6.17 para 3: an event variable compared to itself refers to the same
// synchronization object, so `ev == ev` is true. Observed end-to-end.
TEST(Simulator, EventSelfEqualityObservedEndToEnd) {
  LowerFixture f;
  auto* self_eq = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  bit self_eq;\n"
      "  initial self_eq = (ev == ev);\n"
      "endmodule\n",
      f, "self_eq");
  ASSERT_NE(self_eq, nullptr);
  EXPECT_EQ(self_eq->value.ToUint64(), 1u);
}

// §6.17 para 3: nullifying one handle of an aliased pair breaks only that
// handle's association; the other handle keeps referring to the synchronization
// object. Starting from `event b = a;` (shared), `b = null` leaves `a` bound
// (`a == null` false) while `b` becomes null (`b == null` true) and the two
// handles no longer refer to the same object (`a == b` false). Observed
// end-to-end.
TEST(Simulator, EventNullifyOnAliasBreaksOnlyAssignedName) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a;\n"
      "  event b = a;\n"
      "  bit a_is_null;\n"
      "  bit b_is_null;\n"
      "  bit still_equal;\n"
      "  initial begin\n"
      "    b = null;\n"
      "    a_is_null = (a == null);\n"
      "    b_is_null = (b == null);\n"
      "    still_equal = (a == b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* a_is_null = f.ctx.FindVariable("a_is_null");
  auto* b_is_null = f.ctx.FindVariable("b_is_null");
  auto* still_equal = f.ctx.FindVariable("still_equal");
  ASSERT_NE(a_is_null, nullptr);
  ASSERT_NE(b_is_null, nullptr);
  ASSERT_NE(still_equal, nullptr);
  EXPECT_EQ(a_is_null->value.ToUint64(), 0u);
  EXPECT_EQ(b_is_null->value.ToUint64(), 1u);
  EXPECT_EQ(still_equal->value.ToUint64(), 0u);
}

// §6.17 with §8.5: an event property is an event of the object, so an event
// control on it through a handle, `@(e.ev)`, returns when a trigger through a
// handle, `-> e.ev`, sets it (§9.4.2). With no event behind the property the
// wait stayed parked and the fork never printed.
TEST(Simulator, EventPropertyWaitedAndTriggeredThroughAHandle) {
  SimFixture f;
  auto out = RunCapture(
      "class E; event ev; endclass\n"
      "module t;\n"
      "  E e = new;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin @(e.ev); $display(\"woke %0t\", $time); end\n"
      "    join_none\n"
      "    #1 -> e.ev;\n"
      "    #1 $display(\"done %0t\", $time);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "woke 1\ndone 2\n");
}

// The same inside the class: a method waits on the object's own event by its
// bare name and another method triggers it, as #3719's `-> ev` in a task of
// the class does for a wait written outside it.
TEST(Simulator, EventPropertyWaitedAndTriggeredInsideTheClass) {
  SimFixture f;
  auto out = RunCapture(
      "class O;\n"
      "  event own;\n"
      "  task wait_own(); @(own); $display(\"woke %0t\", $time); endtask\n"
      "  function void fire(); -> own; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  O o = new;\n"
      "  initial begin\n"
      "    fork o.wait_own(); join_none\n"
      "    #1 o.fire();\n"
      "    #1 $display(\"done %0t\", $time);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "woke 1\ndone 2\n");
}

// UVM's uvm_objection::wait_for waits on `@(m_events[obj].all_dropped)`, an
// event property of an object held in an associative array keyed by a
// handle, which m_forked_drain triggers with `->m_events[obj].all_dropped`.
TEST(Simulator, EventPropertyOfAnAssociativeElementWakesItsWaiter) {
  SimFixture f;
  auto out = RunCapture(
      "class E; event all_dropped; endclass\n"
      "class K; endclass\n"
      "class O;\n"
      "  E m_events[K];\n"
      "  task wait_for(K k);\n"
      "    if (!m_events.exists(k)) m_events[k] = new;\n"
      "    @(m_events[k].all_dropped);\n"
      "    $display(\"woke %0t\", $time);\n"
      "  endtask\n"
      "  function void fire(K k); ->m_events[k].all_dropped; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  O o = new;\n"
      "  K k = new;\n"
      "  initial begin\n"
      "    fork o.wait_for(k); join_none\n"
      "    #1 o.fire(k);\n"
      "    #1 $display(\"done %0t\", $time);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "woke 1\ndone 2\n");
}

// Each object's property is an event of its own: triggering a's wakes the
// process waiting on a's and leaves the one waiting on b's parked, so b's
// waiter wakes only at b's trigger a time unit later.
TEST(Simulator, EventPropertiesOfTwoObjectsAreDistinctEvents) {
  SimFixture f;
  auto out = RunCapture(
      "class E; event ev; endclass\n"
      "module t;\n"
      "  E a = new;\n"
      "  E b = new;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin @(a.ev); $display(\"a %0t\", $time); end\n"
      "      begin @(b.ev); $display(\"b %0t\", $time); end\n"
      "    join_none\n"
      "    #1 -> a.ev;\n"
      "    #1 -> b.ev;\n"
      "    #1 $display(\"done %0t\", $time);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a 1\nb 2\ndone 3\n");
}

// §6.17 with §8.9: a static event property is one event for the class and
// every object of it, so a wait by the scope form `@Sync::e` returns at
// `-> Sync::e`, a static task's wait on the bare `e` returns at the same
// trigger, and a wait through an object's handle, `@x.e`, returns at a
// trigger through the handle -- #3924's shapes, which woke nothing.
TEST(Simulator, StaticEventPropertyIsTheClassesOneEvent) {
  SimFixture f;
  auto out = RunCapture(
      "class Sync;\n"
      "  static event e;\n"
      "  static task waiter(); @e; $display(\"task %0t\", $time); endtask\n"
      "endclass\n"
      "module t;\n"
      "  Sync x = new;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin @Sync::e; $display(\"scope %0t\", $time); end\n"
      "      Sync::waiter();\n"
      "      #2 -> Sync::e;\n"
      "    join\n"
      "    fork\n"
      "      begin @x.e; $display(\"handle %0t\", $time); end\n"
      "      #2 -> x.e;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "scope 2\ntask 2\nhandle 4\n");
}

}  // namespace
