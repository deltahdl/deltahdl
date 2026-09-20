#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "helpers_string_var.h"
#include "simulator/sync_objects.h"

using namespace delta;

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

TEST(IpcSync, MailboxParameterizedSameMethodsAsDynamic) {
  MailboxObject mb;

  EXPECT_EQ(mb.Num(), 0);
  EXPECT_EQ(mb.Put(Msg(42).Get()), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.TryPut(Msg(43).Get()), 1);
  EXPECT_EQ(mb.Num(), 2);

  Logic4Snapshot msg;
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(Word(msg), 42u);
  EXPECT_EQ(mb.TryPeek(msg), 1);
  EXPECT_EQ(Word(msg), 42u);
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(msg), 42u);
  EXPECT_EQ(mb.TryGet(msg), 1);
  EXPECT_EQ(Word(msg), 43u);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxParameterizedSameRuntimeAsTypeless) {
  MailboxObject typed_mb(5);
  MailboxObject untyped_mb(5);

  typed_mb.TryPut(Msg(100).Get());
  untyped_mb.TryPut(Msg(100).Get());

  Logic4Snapshot t_msg;
  Logic4Snapshot u_msg;
  typed_mb.TryGet(t_msg);
  untyped_mb.TryGet(u_msg);
  EXPECT_EQ(Word(t_msg), Word(u_msg));
}

// §15.4.9 (printed page 377): a parameterized mailbox provides the same
// methods as the typeless one, so `mailbox #(int)` takes a put() and hands
// the message to get(): 3 and a num() of 0 read as 30. Left unlowered, the
// parameterized declaration created no queue and r read x.
TEST(MailboxSim, ParameterizedMailboxCarriesItsMessages) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox #(int) mb = new;\n"
      "  int a, r;\n"
      "  initial begin\n"
      "    mb.put(3);\n"
      "    mb.get(a);\n"
      "    r = a * 10 + mb.num();\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

// §15.4.9 (printed page 377): the subclause's own form declares the
// parameterized mailbox through a typedef, `typedef mailbox #(string)
// s_mbox; s_mbox sm = new;`, and §6.18 makes the typedef name stand for the
// type it renames, so the declaration creates the mailbox as `mailbox
// #(string) sm = new` does: put("hello") is counted by num() as 1 and get()
// leaves s holding "hello". A declaration the typedef name left uncreated
// put on no queue, counted 0 and left s empty.
TEST(MailboxSim, TypedefdMailboxCarriesItsMessages) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef mailbox #(string) s_mbox;\n"
      "  s_mbox sm = new;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    sm.put(\"hello\");\n"
      "    n = sm.num();\n"
      "    sm.get(s);\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(VecToStr(var->value), "hello");
  auto* n = f.ctx.FindVariable("n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 1u);
}

// §15.4.9 (printed page 377): a mailbox declared through a typedef of
// `mailbox #(string)` is the parameterized mailbox, whose transfer methods
// the compiler verifies, so get() into an int is reported at the call under
// this subclause rather than left to the run.
TEST(MailboxSim, TypedefdMailboxRejectsAGetOfAnotherType) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef mailbox #(string) s_mbox;\n"
      "  s_mbox sm = new;\n"
      "  int n;\n"
      "  initial sm.get(n);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to mailbox method 'get' is not type-equivalent", 5, "15.4.9"));
}

// §15.3.1 (printed page 373) with §6.18: a semaphore declared through a
// typedef, `typedef semaphore sem_t; sem_t s = new(2);`, is created with the
// two keys its new() names. get(1) takes one, try_get(2) then finds one key
// short and answers 0, and try_get(1) takes the last and answers 1: r reads
// 1. A bucket the typedef name left uncreated blocked the get() and left r
// at 0, and one that kept both keys read 10.
TEST(SemaphoreSim, TypedefdSemaphoreHoldsItsKeys) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef semaphore sem_t;\n"
                      "  sem_t s = new(2);\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    s.get(1);\n"
                      "    r = s.try_get(2) * 10 + s.try_get(1);\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            1u);
}

}  // namespace
