// §15.4: Mailboxes

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulation/awaiters.h"
#include "simulation/exec_task.h"
#include "simulation/process.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/stmt_exec.h"
#include "simulation/stmt_result.h"
#include "simulation/sync_objects.h"
#include "simulation/variable.h"
#include <cstdint>
#include <gtest/gtest.h>
#include <string_view>

using namespace delta;

// Helper fixture providing scheduler, arena, diag, and sim context.
struct SyncFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag, 42};
};

namespace {

TEST(IpcSync, MailboxTryGetFifoOrder) {
  MailboxObject mb;
  mb.TryPut(10);
  mb.TryPut(20);
  mb.TryPut(30);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(msg, 10u);
  mb.TryGet(msg);
  EXPECT_EQ(msg, 20u);
  mb.TryGet(msg);
  EXPECT_EQ(msg, 30u);
  EXPECT_EQ(mb.Num(), 0);
}

// =============================================================================
// 10. Mailbox: Context registration (section 15.4)
// =============================================================================
TEST(IpcSync, MailboxContextCreateFind) {
  SyncFixture f;
  auto *mb = f.ctx.CreateMailbox("mbox1", 10);
  ASSERT_NE(mb, nullptr);
  EXPECT_EQ(mb->bound, 10);

  auto *found = f.ctx.FindMailbox("mbox1");
  EXPECT_EQ(found, mb);

  auto *not_found = f.ctx.FindMailbox("no_such_mbox");
  EXPECT_EQ(not_found, nullptr);
}

// =============================================================================
// 12. Mailbox: Multiple get/put cycles
// =============================================================================
TEST(IpcSync, MailboxMultipleGetPutCycles) {
  MailboxObject mb;
  for (uint64_t i = 0; i < 100; ++i) {
    mb.TryPut(i);
  }
  EXPECT_EQ(mb.Num(), 100);
  for (uint64_t i = 0; i < 100; ++i) {
    uint64_t msg = 0;
    EXPECT_EQ(mb.TryGet(msg), 0);
    EXPECT_EQ(msg, i);
  }
  EXPECT_EQ(mb.Num(), 0);
}

// =============================================================================
// 15. Mailbox: IsFull predicate
// =============================================================================
TEST(IpcSync, MailboxIsFullBounded) {
  MailboxObject mb(2);
  EXPECT_FALSE(mb.IsFull());
  mb.TryPut(1);
  EXPECT_FALSE(mb.IsFull());
  mb.TryPut(2);
  EXPECT_TRUE(mb.IsFull());
}

TEST(IpcSync, MailboxIsFullUnbounded) {
  MailboxObject mb;
  EXPECT_FALSE(mb.IsFull());
  for (int i = 0; i < 1000; ++i) {
    mb.TryPut(static_cast<uint64_t>(i));
  }
  EXPECT_FALSE(mb.IsFull()); // Unbounded never full.
}

// =============================================================================
// 19. Mailbox: Parameterized type simulation (uint64_t values)
// =============================================================================
TEST(IpcSync, MailboxParameterizedTypeValues) {
  MailboxObject mb;
  // Simulate different "types" by encoding type info in the value.
  mb.TryPut(0xDEADBEEF);
  mb.TryPut(0xCAFEBABE);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(msg, 0xDEADBEEFu);
  mb.TryGet(msg);
  EXPECT_EQ(msg, 0xCAFEBABEu);
}

// =============================================================================
// 24. Multiple mailboxes in same context
// =============================================================================
TEST(IpcSync, MultipleMailboxesInContext) {
  SyncFixture f;
  auto *mb1 = f.ctx.CreateMailbox("m1", 0);
  auto *mb2 = f.ctx.CreateMailbox("m2", 3);
  mb1->TryPut(100);
  mb2->TryPut(200);
  uint64_t msg = 0;
  mb1->TryGet(msg);
  EXPECT_EQ(msg, 100u);
  mb2->TryGet(msg);
  EXPECT_EQ(msg, 200u);
}

} // namespace
