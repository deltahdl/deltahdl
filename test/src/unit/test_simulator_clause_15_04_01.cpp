#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/awaiters.h"
#include "simulator/exec_task.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/sync_objects.h"

namespace {

TEST(IpcSync, MailboxNewUnbounded) {
  MailboxObject mb;
  EXPECT_EQ(mb.bound, 0);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxNewBounded) {
  MailboxObject mb(5);
  EXPECT_EQ(mb.bound, 5);
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
  EXPECT_EQ(mb.TryPut(42), 1);
  EXPECT_TRUE(mb.IsFull());
  EXPECT_EQ(mb.TryPut(99), 0);
}

// §15.4.1: a nonzero bound is the size of the mailbox queue. Confirm that a
// bound of three (not the degenerate one) becomes full only on the third
// message, so the capacity tracks the bound value itself rather than a fixed
// limit.
TEST(IpcSync, MailboxNewBoundedFillsAtBoundValue) {
  MailboxObject mb(3);
  EXPECT_EQ(mb.bound, 3);
  EXPECT_EQ(mb.TryPut(10), 1);
  EXPECT_FALSE(mb.IsFull());
  EXPECT_EQ(mb.TryPut(20), 1);
  EXPECT_FALSE(mb.IsFull());
  EXPECT_EQ(mb.TryPut(30), 1);
  EXPECT_TRUE(mb.IsFull());
  EXPECT_EQ(mb.Num(), 3);
  EXPECT_EQ(mb.TryPut(40), 0);
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

// §15.4.1: a negative bound is illegal; this implementation resolves the
// indeterminate case by treating it as unbounded. Drive that through the
// context creation path to confirm the clamp applies to the handle new() hands
// back.
TEST(IpcSync, MailboxNewContextNegativeBoundClampsToZero) {
  SyncFixture f;
  auto* mb = f.ctx.CreateMailbox("mb_neg", -4);
  ASSERT_NE(mb, nullptr);
  EXPECT_EQ(mb->bound, 0);
  EXPECT_FALSE(mb->IsFull());
}

// §15.4.1: a mailbox created with bound 0 is unbounded, so a put never blocks.
// Stuff far more messages than any bounded queue would admit and confirm every
// placement succeeds without ever requesting suspension.
TEST(IpcSync, MailboxNewUnboundedPutNeverBlocks) {
  MailboxObject mb;  // default bound 0 -> unbounded
  for (int i = 0; i < 1000; ++i) {
    EXPECT_EQ(mb.Put(static_cast<uint64_t>(i)), MbxPutStatus::kPlaced);
    EXPECT_FALSE(mb.IsFull());
  }
  EXPECT_EQ(mb.Num(), 1000);
}

}  // namespace
