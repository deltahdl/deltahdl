#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/stmt_exec.h"
#include "simulator/sync_objects.h"

namespace {

// A 64-bit two-state message holding `v`, as the C++ cases below place one,
// and the low word of a message read back out of the queue.
Logic4Snapshot Msg(uint64_t v) {
  Logic4Word word{v, 0};
  Logic4Vec vec{64, 1, &word};
  Logic4Snapshot snap;
  snap.Capture(vec);
  return snap;
}

uint64_t Word(const Logic4Snapshot& msg) { return msg.Get().ToUint64(); }

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

// §15.4.1: a nonzero bound is the size of the mailbox queue. Confirm that a
// bound of three (not the degenerate one) becomes full only on the third
// message, so the capacity tracks the bound value itself rather than a fixed
// limit.
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

// §15.4.1: new() returns the mailbox handle, and a nonzero bound is the size of
// the queue. Exercise the context creation path (the production site driven by
// a language-level new(N)) with a positive bound and confirm the returned
// handle carries that bound and fills exactly at it.
TEST(IpcSync, MailboxNewContextBounded) {
  SyncFixture f;
  auto* mb = f.ctx.CreateMailbox("mb_b", 2);
  ASSERT_NE(mb, nullptr);
  EXPECT_EQ(mb->bound, 2);
  EXPECT_FALSE(mb->IsFull());
  EXPECT_EQ(mb->TryPut(7), 1);
  EXPECT_FALSE(mb->IsFull());
  EXPECT_EQ(mb->TryPut(8), 1);
  EXPECT_TRUE(mb->IsFull());
}

// §15.4.1: a mailbox created with bound 0 is unbounded, so a put never blocks.
// Stuff far more messages than any bounded queue would admit and confirm every
// placement succeeds without ever requesting suspension.
TEST(IpcSync, MailboxNewUnboundedPutNeverBlocks) {
  MailboxObject mb;  // default bound 0 -> unbounded
  for (int i = 0; i < 1000; ++i) {
    EXPECT_EQ(mb.Put(Msg(static_cast<uint64_t>(i)).Get()),
              MbxPutStatus::kPlaced);
    EXPECT_FALSE(mb.IsFull());
  }
  EXPECT_EQ(mb.Num(), 1000);
}

// §15.4.1: the never-block property of an unbounded mailbox is a consequence of
// the bound value chosen at new(), not an inherent property of put(). Isolate
// that link by giving new() a nonzero bound and driving put() (the blocking
// method, not the try_ variant) once the queue is full: it must report a block,
// leaving the queue untouched. Paired with MailboxNewUnboundedPutNeverBlocks
// this proves the constructor's bound argument alone governs whether put() can
// block.
TEST(IpcSync, MailboxNewBoundedPutBlocksWhenFull) {
  MailboxObject mb(2);  // nonzero bound -> queue size is 2
  EXPECT_EQ(mb.Put(Msg(11).Get()), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(Msg(22).Get()), MbxPutStatus::kPlaced);
  EXPECT_TRUE(mb.IsFull());
  EXPECT_EQ(mb.Put(Msg(33).Get()), MbxPutStatus::kBlock);
  EXPECT_EQ(mb.Num(), 2);
}

// The tests above drive MailboxObject from C++. The ones below state the
// rules as SystemVerilog, where §15.4 makes its claim; no language-level
// mailbox was lowered at all, so `mailbox mb = new;` created no queue and
// every method on mb reached nothing.

// §15.4.1 (printed page 374): new() with no bound builds an unbounded mailbox
// and a put() on it never blocks, so two messages go in, get() takes the
// first in the order they were placed (§15.4.3) and num() counts the one
// left (§15.4.2): 7 and 1 read as 71. Left unlowered, the get() stored
// nothing and r read x.
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

// §15.4.1 (printed page 374): a nonzero bound is the size of the queue, and
// the mailbox may be built by an assignment rather than a declaration
// initializer. Built with new(1) procedurally, the first try_put() places
// its message and the second finds the queue full (§15.4.4): 1 and 0 read as
// 10. A bound that did not reach the queue would have read 11.
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

// §15.4.1 (printed page 374) with §23.9: a mailbox declared inside a module
// instance is the instance's own, created under the instance's key, and a
// bare `mb` inside M names it. Asked by the bare key alone, no mailbox
// answered the name inside the instance, so put() and get() ran on none and
// r read x; here get() retrieves the 6 put() placed and num() counts none
// left: 60.
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

}  // namespace
