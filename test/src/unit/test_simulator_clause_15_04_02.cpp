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

TEST(IpcSync, MailboxNumReflectsState) {
  MailboxObject mb;
  EXPECT_EQ(mb.Num(), 0);
  mb.TryPut(1);
  EXPECT_EQ(mb.Num(), 1);
  mb.TryPut(2);
  EXPECT_EQ(mb.Num(), 2);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(mb.Num(), 1);
  mb.TryGet(msg);
  EXPECT_EQ(mb.Num(), 0);
}

// §15.4.2: num() on a fresh mailbox returns 0.
TEST(IpcSync, MailboxNumEmptyReturnsZero) {
  MailboxObject mb;
  EXPECT_EQ(mb.Num(), 0);
}

// §15.4.2: num() on a bounded mailbox at capacity.
TEST(IpcSync, MailboxNumAtBound) {
  MailboxObject mb(3);
  mb.TryPut(1);
  mb.TryPut(2);
  mb.TryPut(3);
  EXPECT_EQ(mb.Num(), 3);
  EXPECT_EQ(mb.TryPut(4), -1);
  EXPECT_EQ(mb.Num(), 3);
}

// §15.4.2: num() is invalidated by get() — value changes after removal.
TEST(IpcSync, MailboxNumInvalidatedByGet) {
  MailboxObject mb;
  mb.TryPut(10);
  mb.TryPut(20);
  int32_t before = mb.Num();
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_NE(mb.Num(), before);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.2: num() is invalidated by put() — value changes after insertion.
TEST(IpcSync, MailboxNumInvalidatedByPut) {
  MailboxObject mb;
  mb.TryPut(10);
  int32_t before = mb.Num();
  mb.TryPut(20);
  EXPECT_NE(mb.Num(), before);
  EXPECT_EQ(mb.Num(), 2);
}

}  // namespace
