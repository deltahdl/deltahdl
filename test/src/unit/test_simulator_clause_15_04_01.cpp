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

// §15.4.1: Negative bound is illegal; clamp to 0 (unbounded).
TEST(IpcSync, MailboxNewNegativeBoundClampsToZero) {
  MailboxObject mb(-3);
  EXPECT_EQ(mb.bound, 0);
  EXPECT_FALSE(mb.IsFull());
}

// §15.4.1: Bound of 1 creates a single-slot mailbox.
TEST(IpcSync, MailboxNewBoundOne) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.bound, 1);
  EXPECT_EQ(mb.TryPut(42), 1);
  EXPECT_TRUE(mb.IsFull());
  EXPECT_EQ(mb.TryPut(99), 0);
}

// §15.4.1: CreateMailbox in context with bound 0 is unbounded.
TEST(IpcSync, MailboxNewContextUnbounded) {
  SyncFixture f;
  auto* mb = f.ctx.CreateMailbox("mb_ub", 0);
  ASSERT_NE(mb, nullptr);
  EXPECT_EQ(mb->bound, 0);
  EXPECT_FALSE(mb->IsFull());
}

}  // namespace
