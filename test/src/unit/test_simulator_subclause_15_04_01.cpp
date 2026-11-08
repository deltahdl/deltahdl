#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/stmt_exec.h"
#include "simulator/sync_objects.h"

namespace {

Logic4Snapshot Msg(uint64_t v) {
  Logic4Word word{v, 0};
  Logic4Vec vec{64, 1, &word};
  Logic4Snapshot snap;
  snap.Capture(vec);
  return snap;
}

TEST(IpcSync, MailboxNewUnbounded) {
  MailboxObject mb;
  EXPECT_EQ(mb.bound, 0);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxNewNegativeBoundClampsToZero) {
  MailboxObject mb(-3);
  EXPECT_EQ(mb.bound, 0);
  EXPECT_FALSE(mb.IsFull());
}

TEST(IpcSync, MailboxNewBoundOne) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.bound, 1);
  EXPECT_EQ(mb.TryPut(Msg(42).Get()), 1);
  EXPECT_TRUE(mb.IsFull());
  EXPECT_EQ(mb.TryPut(Msg(99).Get()), 0);
}

TEST(IpcSync, MailboxNewBoundedFillsAtBoundValue) {
  MailboxObject mb(3);
  EXPECT_EQ(mb.bound, 3);
  EXPECT_EQ(mb.TryPut(Msg(10).Get()), 1);
  EXPECT_FALSE(mb.IsFull());
  EXPECT_EQ(mb.TryPut(Msg(20).Get()), 1);
  EXPECT_FALSE(mb.IsFull());
  EXPECT_EQ(mb.TryPut(Msg(30).Get()), 1);
  EXPECT_TRUE(mb.IsFull());
  EXPECT_EQ(mb.Num(), 3);
  EXPECT_EQ(mb.TryPut(Msg(40).Get()), 0);
}

TEST(IpcSync, MailboxNewContextUnbounded) {
  SyncFixture f;
  auto* mb = f.ctx.CreateMailbox("mb_ub", 0);
  ASSERT_NE(mb, nullptr);
  EXPECT_EQ(mb->bound, 0);
  EXPECT_FALSE(mb->IsFull());
}

TEST(IpcSync, MailboxNewContextBounded) {
  SyncFixture f;
  auto* mb = f.ctx.CreateMailbox("mb_b", 2);
  ASSERT_NE(mb, nullptr);
  EXPECT_EQ(mb->bound, 2);
  EXPECT_FALSE(mb->IsFull());
  EXPECT_EQ(mb->TryPut(Msg(7).Get()), 1);
  EXPECT_FALSE(mb->IsFull());
  EXPECT_EQ(mb->TryPut(Msg(8).Get()), 1);
  EXPECT_TRUE(mb->IsFull());
}

TEST(IpcSync, MailboxNewUnboundedPutNeverBlocks) {
  MailboxObject mb;
  for (int i = 0; i < 1000; ++i) {
    EXPECT_EQ(mb.Put(Msg(static_cast<uint64_t>(i)).Get()),
              MbxPutStatus::kPlaced);
    EXPECT_FALSE(mb.IsFull());
  }
  EXPECT_EQ(mb.Num(), 1000);
}

TEST(IpcSync, MailboxNewBoundedPutBlocksWhenFull) {
  MailboxObject mb(2);
  EXPECT_EQ(mb.Put(Msg(11).Get()), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(Msg(22).Get()), MbxPutStatus::kPlaced);
  EXPECT_TRUE(mb.IsFull());
  EXPECT_EQ(mb.Put(Msg(33).Get()), MbxPutStatus::kBlock);
  EXPECT_EQ(mb.Num(), 2);
}

TEST(MailboxSim, NewUnboundedTakesMessagesWithoutLimit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  int a, r;\n"
      "  initial begin\n"
      "    mb.put(7);\n"
      "    mb.put(9);\n"
      "    mb.get(a);\n"
      "    r = a * 10 + mb.num();\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 71u);
}

TEST(MailboxSim, NewAssignmentBoundsTheQueue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb;\n"
      "  int first, second, r;\n"
      "  initial begin\n"
      "    mb = new(1);\n"
      "    first = mb.try_put(3);\n"
      "    second = mb.try_put(4);\n"
      "    r = first * 10 + second;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(MailboxSim, ChildInstanceQueueAnswersItsBareName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  mailbox mb = new;\n"
      "  int a, r;\n"
      "  initial begin\n"
      "    mb.put(6);\n"
      "    mb.get(a);\n"
      "    r = a * 10 + mb.num();\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("m.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 60u);
}

TEST(MailboxSim, ClassPropertyMailboxIsBuiltPerObject) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  mailbox mb = new;\n"
                      "  semaphore s = new(1);\n"
                      "  function void give(int v);\n"
                      "    mb.put(v);\n"
                      "  endfunction\n"
                      "  function int take();\n"
                      "    int v;\n"
                      "    mb.get(v);\n"
                      "    return v;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  int n, v, y;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.give(4);\n"
                      "    n = c.mb.num();\n"
                      "    v = c.take();\n"
                      "    y = v * 10 + n;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            41u);
}

TEST(MailboxSim, TwoObjectsHoldSeparateMailboxes) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  mailbox mb = new;\n"
                      "  function void give(int v);\n"
                      "    mb.put(v);\n"
                      "  endfunction\n"
                      "  function int take();\n"
                      "    int v;\n"
                      "    mb.get(v);\n"
                      "    return v;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static C c1 = new;\n"
                      "    static C c2 = new;\n"
                      "    c2.give(2);\n"
                      "    c1.give(1);\n"
                      "    y = c1.take() * 10 + c2.take();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            12u);
}

TEST(MailboxSim, ThisAndHandleQualifiedPropertyMailboxReceivers) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  mailbox mb = new;\n"
                      "  function void give(int v);\n"
                      "    this.mb.put(v);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  int y, v;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.give(4);\n"
                      "    c.give(5);\n"
                      "    y = c.mb.num() * 10;\n"
                      "    c.mb.get(v);\n"
                      "    y = y + v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            24u);
}

TEST(MailboxSim, BoundedPropertyMailboxPutWaitsForTheModulesGet) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  mailbox mb = new(1);\n"
                      "  task fill();\n"
                      "    mb.put(1);\n"
                      "    mb.put(2);\n"
                      "  endtask\n"
                      "endclass\n"
                      "module top;\n"
                      "  int got, at, r;\n"
                      "  C c;\n"
                      "  initial begin\n"
                      "    c = new;\n"
                      "    fork\n"
                      "      begin\n"
                      "        c.fill();\n"
                      "        at = $time;\n"
                      "      end\n"
                      "      #5 c.mb.get(got);\n"
                      "    join\n"
                      "    r = got * 10 + at;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            15u);
}

TEST(MailboxSim, TryPutOnAFullPropertyMailboxReadsZero) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  mailbox mb = new(1);\n"
                      "  function int fill();\n"
                      "    return mb.try_put(1) * 10 + mb.try_put(2);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    y = c.fill();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

TEST(MailboxSim, PropertyMailboxBuiltByAssignmentInTheConstructor) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  mailbox mb;\n"
                      "  function new();\n"
                      "    mb = new(1);\n"
                      "  endfunction\n"
                      "  function int fill();\n"
                      "    return mb.try_put(1) * 10 + mb.try_put(2);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    y = c.fill();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

TEST(MailboxSim, PutThroughANullPropertyMailboxIsReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  mailbox mb;\n"
      "  function void give(int v);\n"
      "    mb.put(v);\n"
      "  endfunction\n"
      "endclass\n"
      "module top;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.give(4);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'put' called through the null handle 'mb'",
                            4, "8.4"));
}

std::string TypedefdMailboxPropertySrc(const std::string& head,
                                       const std::string& type) {
  return head + "class C;\n  " + type +
         " mb = new;\n"
         "  function void give(int v);\n"
         "    mb.put(v);\n"
         "  endfunction\n"
         "  function int take();\n"
         "    int v;\n"
         "    mb.get(v);\n"
         "    return v;\n"
         "  endfunction\n"
         "endclass\n"
         "module top;\n"
         "  int y, v, n;\n"
         "  C c;\n"
         "  initial begin\n"
         "    c = new;\n"
         "    c.give(4);\n"
         "    c.give(5);\n"
         "    n = c.mb.num();\n"
         "    v = c.take();\n"
         "    y = v * 10 + n;\n"
         "  end\n"
         "endmodule\n";
}

TEST(MailboxSim, TypedefdMailboxPropertyIsBuiltPerObject) {
  EXPECT_EQ(RunAndGet(TypedefdMailboxPropertySrc(
                          "typedef mailbox #(int) mb_t;\n", "mb_t"),
                      "y"),
            42u);
}

TEST(MailboxSim, PackageTypedefdMailboxPropertyIsBuiltPerObject) {
  EXPECT_EQ(
      RunAndGet(TypedefdMailboxPropertySrc("package p;\n"
                                           "  typedef mailbox #(int) mb_t;\n"
                                           "endpackage\n",
                                           "p::mb_t"),
                "y"),
      42u);
}

TEST(MailboxSim, TypedefOfATypedefdMailboxPropertyIsBuiltPerObject) {
  EXPECT_EQ(
      RunAndGet(TypedefdMailboxPropertySrc("typedef mailbox #(int) mb_t;\n"
                                           "typedef mb_t mb2_t;\n",
                                           "mb2_t"),
                "y"),
      42u);
}

TEST(MailboxSim, StaticMailboxPropertyIsSharedByEveryObject) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static mailbox mb = new;\n"
                      "  function void give(int v);\n"
                      "    mb.put(v);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static C c1 = new;\n"
                      "    static C c2 = new;\n"
                      "    c1.give(1);\n"
                      "    c2.give(2);\n"
                      "    y = C::mb.num() * 10 + c2.mb.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            22u);
}

TEST(MailboxSim, StaticMethodPutsIntoTheStaticMailboxProperty) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static mailbox mb = new;\n"
                      "  static function void give_all(int v);\n"
                      "    mb.put(v);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  int v, y;\n"
                      "  initial begin\n"
                      "    C::give_all(3);\n"
                      "    C::give_all(4);\n"
                      "    C::mb.get(v);\n"
                      "    y = v * 10 + C::mb.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            31u);
}

TEST(MailboxSim, ConstructorTakesTheModulesMailboxAsAHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  mailbox mb;\n"
                      "  function new(mailbox m);\n"
                      "    mb = m;\n"
                      "  endfunction\n"
                      "  function void give(int v);\n"
                      "    mb.put(v);\n"
                      "  endfunction\n"
                      "  function int take();\n"
                      "    int v;\n"
                      "    mb.get(v);\n"
                      "    return v;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  mailbox shared = new;\n"
                      "  int n, v, y;\n"
                      "  initial begin\n"
                      "    static C c1 = new(shared);\n"
                      "    static C c2 = new(shared);\n"
                      "    c1.give(1);\n"
                      "    c2.give(2);\n"
                      "    n = shared.num();\n"
                      "    v = c1.take();\n"
                      "    y = n * 10 + v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            21u);
}

TEST(MailboxSim, PropertyHandleAssignedFromAnotherObjectShares) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  mailbox mb = new;\n"
                      "  function void give(int v);\n"
                      "    mb.put(v);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static C c1 = new;\n"
                      "    static C c2 = new;\n"
                      "    c2.mb = c1.mb;\n"
                      "    c2.give(5);\n"
                      "    c2.give(6);\n"
                      "    y = c1.mb.num() * 10 + c2.mb.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            22u);
}

TEST(MailboxSim, PropertyInitializedFromTheModulesMailboxSharesIt) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  mailbox shared = new;\n"
                      "  class C;\n"
                      "    mailbox mb = shared;\n"
                      "    function void give(int v);\n"
                      "      mb.put(v);\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "  int v, y;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.give(7);\n"
                      "    c.give(8);\n"
                      "    shared.get(v);\n"
                      "    y = v * 10 + shared.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            71u);
}

TEST(MailboxSim, PutThroughAMailboxFormalReachesTheActual) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  mailbox shared = new;\n"
                      "  int v, y;\n"
                      "  function void send(mailbox m, int val);\n"
                      "    m.put(val);\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    send(shared, 9);\n"
                      "    send(shared, 8);\n"
                      "    shared.get(v);\n"
                      "    y = v * 10 + shared.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            91u);
}

TEST(MailboxSim, PropertyMailboxComparesWithNullByTheObjectItHolds) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  mailbox built = new;\n"
                      "  mailbox bare;\n"
                      "  function int probe();\n"
                      "    int r = 0;\n"
                      "    if (built == null) r = r + 1;\n"
                      "    if (bare == null) r = r + 10;\n"
                      "    if (built != null) r = r + 100;\n"
                      "    if (built) r = r + 1000;\n"
                      "    return r;\n"
                      "  endfunction\n"
                      "  function void drop();\n"
                      "    built = null;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    y = c.probe();\n"
                      "    if (c.built != null) y = y + 10000;\n"
                      "    if (c.bare == null) y = y + 100000;\n"
                      "    c.drop();\n"
                      "    if (c.built == null) y = y + 1000000;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            1111110u);
}

TEST(MailboxSim, NestedClassMethodPutsIntoTheEnclosingClassStaticMailbox) {
  EXPECT_EQ(RunAndGet("class Outer;\n"
                      "  static mailbox mb = new;\n"
                      "  class Inner;\n"
                      "    function void give(int v);\n"
                      "      mb.put(v);\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endclass\n"
                      "module top;\n"
                      "  int v, y;\n"
                      "  initial begin\n"
                      "    static Outer::Inner i = new;\n"
                      "    i.give(4);\n"
                      "    y = Outer::mb.num() * 10;\n"
                      "    Outer::mb.get(v);\n"
                      "    y = y + v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            14u);
}

std::string StaticMailboxBoundedByKSrc(const std::string& head,
                                       const std::string& type) {
  return "package p;\n  int K = 1;\n" + head + "  class C;\n    static " +
         type +
         " mb = new(K);\n"
         "  endclass\n"
         "endpackage\n"
         "module top;\n"
         "  import p::*;\n"
         "  int a, b, y;\n"
         "  initial begin\n"
         "    K = 3;\n"
         "    a = C::mb.try_put(1);\n"
         "    b = C::mb.try_put(2);\n"
         "    y = a * 10 + b;\n"
         "  end\n"
         "endmodule\n";
}

TEST(MailboxSim, StaticMailboxPropertyIsBuiltAtStaticInitialization) {
  EXPECT_EQ(RunAndGet(StaticMailboxBoundedByKSrc("", "mailbox"), "y"), 10u);
}

TEST(MailboxSim, StaticTypedefdMailboxPropertyIsBuiltAtStaticInitialization) {
  EXPECT_EQ(
      RunAndGet(StaticMailboxBoundedByKSrc("  typedef mailbox mb_t;\n", "mb_t"),
                "y"),
      10u);
}

TEST(MailboxSim, ModuleMailboxVariableIsNullUntilNew) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  mailbox bare;\n"
                      "  mailbox built = new;\n"
                      "  mailbox other;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    y = 0;\n"
                      "    if (bare == null) y = y + 1;\n"
                      "    if (bare) y = y + 10;\n"
                      "    if (built != null) y = y + 100;\n"
                      "    if (built) y = y + 1000;\n"
                      "    bare = new(2);\n"
                      "    if (bare != null) y = y + 10000;\n"
                      "    if (bare == null) y = y + 100000;\n"
                      "    other = built;\n"
                      "    if (other != null) y = y + 1000000;\n"
                      "    built = null;\n"
                      "    if (built == null) y = y + 10000000;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            11011101u);
}

TEST(MailboxSim, ModuleMailboxNewInProcessBoundsTheQueueItMakesHeld) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  mailbox bare;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    bare = new(2);\n"
                      "    y = bare.try_put(1) * 100 + bare.try_put(2) * 10 +\n"
                      "        bare.try_put(3);\n"
                      "    if (bare != null) y = y + 1000;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            1110u);
}

TEST(MailboxSim, MailboxHandlesCompareByTheQueueEachRefersTo) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  mailbox x = new;\n"
                      "  mailbox y = new;\n"
                      "endclass\n"
                      "module top;\n"
                      "  mailbox a = new;\n"
                      "  mailbox b = new;\n"
                      "  mailbox c;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    static C o = new;\n"
                      "    r = 0;\n"
                      "    if (a == b) r = r + 1;\n"
                      "    c = a;\n"
                      "    if (c == a) r = r + 10;\n"
                      "    if (c != b) r = r + 100;\n"
                      "    if (o.x == o.y) r = r + 1000;\n"
                      "    o.y = o.x;\n"
                      "    if (o.x == o.y) r = r + 10000;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            10110u);
}

TEST(MailboxSim, AutomaticTaskLocalMailboxHoldsItsOwnQueue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int n, v, r;\n"
      "  task automatic go(output int cnt, output int got);\n"
      "    mailbox m = new;\n"
      "    m.put(3); m.put(4);\n"
      "    cnt = m.num();\n"
      "    m.get(got);\n"
      "  endtask\n"
      "  initial begin\n"
      "    go(n, v);\n"
      "    r = n * 10 + v;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 23u);
}

TEST(MailboxSim, FixedArrayElementIsGivenItsMailbox) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  mailbox mb[2];\n"
                       "  int n, ok, v;\n"
                       "  initial begin\n"
                       "    mb[0] = new;\n"
                       "    mb[0].put(37);\n"
                       "    n = mb[0].num();\n"
                       "    ok = mb[0].try_get(v);\n"
                       "    $display(\"n=%0d ok=%0d v=%0d\", n, ok, v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=1 ok=1 v=37\n");
}

}  // namespace
