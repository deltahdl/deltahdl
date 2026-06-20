#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/sync_objects.h"

using namespace delta;

namespace {

TEST(IpcSync, MailboxParameterizedSameMethodsAsDynamic) {
  MailboxObject mb;

  EXPECT_EQ(mb.Num(), 0);
  EXPECT_EQ(mb.Put(42), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.TryPut(43), 1);
  EXPECT_EQ(mb.Num(), 2);

  uint64_t msg = 0;
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.TryPeek(msg), 1);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.TryGet(msg), 1);
  EXPECT_EQ(msg, 43u);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxParameterizedSameRuntimeAsTypeless) {
  MailboxObject typed_mb(5);
  MailboxObject untyped_mb(5);

  typed_mb.TryPut(100);
  untyped_mb.TryPut(100);

  uint64_t t_msg = 0;
  uint64_t u_msg = 0;
  typed_mb.TryGet(t_msg);
  untyped_mb.TryGet(u_msg);
  EXPECT_EQ(t_msg, u_msg);
}

// Arbitrary, distinct type ids standing in for two non-equivalent data types.
constexpr uint32_t kTypeInt = 1;
constexpr uint32_t kTypeString = 2;

// §15.4.9: a parameterized mailbox fixes its element type and verifies argument
// types against it, so an equivalent type is accepted and a non-equivalent one
// is rejected — the check the compiler applies up front for mailbox #(T).
TEST(IpcSync, MailboxParameterizedAcceptsOnlyMatchingType) {
  MailboxObject mb;
  mb.param_type = kTypeInt;
  EXPECT_TRUE(mb.AcceptsType(kTypeInt));
  EXPECT_FALSE(mb.AcceptsType(kTypeString));
}

// §15.4.9: the default mailbox is typeless (dynamic_type), so it accepts any
// type — no compile-time constraint is imposed.
TEST(IpcSync, MailboxDynamicAcceptsAnyType) {
  MailboxObject mb;  // param_type defaults to kAnyType (dynamic_type).
  EXPECT_TRUE(mb.AcceptsType(kTypeInt));
  EXPECT_TRUE(mb.AcceptsType(kTypeString));
}

// §15.4.9: because a parameterized mailbox only ever transfers values of its
// element type, retrieval through the shared run-time check never reports a
// mismatch — the mismatch a dynamic mailbox would surface at run time is
// instead ruled out up front.
TEST(IpcSync, MailboxParameterizedTransferNeverTypeErrors) {
  MailboxObject mb;
  mb.param_type = kTypeInt;
  ASSERT_TRUE(mb.AcceptsType(kTypeInt));
  mb.TryPut(0xAB, mb.param_type);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Get(msg, mb.param_type), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 0xABu);
}

}  // namespace
