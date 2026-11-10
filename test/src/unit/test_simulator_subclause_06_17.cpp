#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

TEST(Simulator, StaticEventPropertyIsTheClassesOneEvent) {
  SimFixture f;
  auto out = RunCapture(
      "class Sync;\n"
      "  static event e;\n"
      "  static task waiter(); @e; $display(\"task %0t\", $time); endtask\n"
      "  static task fire(); -> e; endtask\n"
      "endclass\n"
      "module t;\n"
      "  Sync x = new;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin @Sync::e; $display(\"scope %0t\", $time); end\n"
      "      Sync::waiter();\n"
      "      #2 Sync::fire();\n"
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

TEST(EventDataType, EventsDeclaredWithoutAnInitializerAreDistinctInEveryPlace) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "package k;\n  event pa, pb;\n  task fire();\n    -> pa;\n"
          "  endtask\nendpackage\n"
          "event ua, ub;\n"
          "interface ifc;\n  event a, b;\nendinterface\n"
          "class C;\n  event e;\nendclass\n"
          "module t;\n  ifc i();\n  if (1) begin : g\n    event a, b;\n  end\n"
          "  event arr[2];\n  C c1 = new, c2 = new;\n"
          "  int w_pb, w_ub, w_ib, w_gb, w_arr, w_c;\n"
          "  int h_pa, h_ua, h_ia, h_ga, h_arr, h_c;\n"
          "  initial begin @(k::pb); w_pb = 1; end\n"
          "  initial begin @(ub); w_ub = 1; end\n"
          "  initial begin @(i.b); w_ib = 1; end\n"
          "  initial begin @(g.b); w_gb = 1; end\n"
          "  initial begin @(arr[1]); w_arr = 1; end\n"
          "  initial begin @(c2.e); w_c = 1; end\n"
          "  initial begin @(k::pa); h_pa = 1; end\n"
          "  initial begin @(ua); h_ua = 1; end\n"
          "  initial begin @(i.a); h_ia = 1; end\n"
          "  initial begin @(g.a); h_ga = 1; end\n"
          "  initial begin @(arr[0]); h_arr = 1; end\n"
          "  initial begin @(c1.e); h_c = 1; end\n"
          "  initial begin\n    #1;\n    k::fire();\n    -> ua;\n    -> i.a;\n"
          "    -> g.a;\n    -> arr[0];\n    -> c1.e;\n"
          "    #1 $display(\"%0d%0d%0d%0d%0d%0d %0d%0d%0d%0d%0d%0d\", "
          "w_pb, w_ub, w_ib, w_gb, w_arr, w_c, h_pa, h_ua, h_ia, h_ga, "
          "h_arr, h_c);\n"
          "  end\nendmodule\n",
          f),
      "000000 111111\n");
}

TEST(EventDataType,
     AnAliasWakesTheOriginalsWaiterAndNullingOneNameKeepsTheOther) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n  event done;\n  event done_too = done;\n"
                       "  event a, b;\n  int w_alias, w_a;\n"
                       "  initial begin @(done_too); w_alias = 1; end\n"
                       "  initial begin b = a; b = null; end\n"
                       "  initial begin #1 @(a); w_a = 1; end\n"
                       "  initial begin\n    #2;\n    -> done;\n    -> a;\n"
                       "    $display(\"%0d\", a.triggered);\n"
                       "    #1 $display(\"%0d %0d %0d %0d\", w_alias, w_a, "
                       "a.triggered, b == null);\n"
                       "  end\nendmodule\n",
                       f),
            "1\n1 1 0 1\n");
}

TEST(EventDataType,
     DISABLED_EventsReachedThroughADottedNameOrElementCompareByObject) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "package k;\n  event pa, pb;\nendpackage\n"
          "class C;\n  event e;\nendclass\n"
          "interface ifc;\n  event a, b;\nendinterface\n"
          "module t;\n  ifc i();\n  if (1) begin : g\n    event a, b;\n  end\n"
          "  typedef struct { event e; } S;\n  S s1, s2;\n  event arr[2];\n"
          "  event y;\n  C c1 = new, c2 = new;\n"
          "  initial begin\n"
          "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", c1.e == c2.e, "
          "arr[0] != arr[1], k::pa != k::pb, i.a === i.b, g.a == g.b, "
          "s1.e == s2.e, k::pa == null);\n"
          "    y = i.a;\n    $display(\"%0d %0d\", y == i.a, y == i.b);\n"
          "  end\nendmodule\n",
          f),
      "0 1 1 0 0 0 0\n1 0\n");
}

TEST(EventDataType, DISABLED_AnEventMemberOfAStructureIsTriggeredAndWaitedFor) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n  typedef struct { event e; int k; } S;\n"
                 "  S s1, s2;\n  S sa[2];\n  int w1, w2, wa;\n"
                 "  initial begin @(s1.e); w1 = 1; end\n"
                 "  initial begin @(s2.e); w2 = 1; end\n"
                 "  initial begin @(sa[1].e); wa = 1; end\n"
                 "  initial begin\n    #1;\n    -> s1.e;\n    -> sa[1].e;\n"
                 "    $display(\"%0d %0d\", s1.e.triggered, "
                 "sa[1].e.triggered);\n"
                 "    #1 $display(\"%0d %0d %0d\", w1, w2, wa);\n"
                 "  end\nendmodule\n",
                 f),
      "1 1\n1 0 1\n");
}

}  // namespace
