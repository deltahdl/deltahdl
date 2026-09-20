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

// A 64-bit two-state message holding `v`, as the C++ cases below place one.
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
  EXPECT_EQ(mb->TryPut(Msg(7).Get()), 1);
  EXPECT_FALSE(mb->IsFull());
  EXPECT_EQ(mb->TryPut(Msg(8).Get()), 1);
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

// §15.4.1 (printed page 374) with §8.7 (printed 184): a mailbox declared as
// a class property with `= new` is built when the object is constructed, so
// the object's methods pass messages through the object's own queue and
// `c.mb.num()` from the module counts what is in it: give(4) places 4,
// num() counts the one message, then take() retrieves it, so v and n read
// as 41. Each reading is a statement of its own because §11.4 fixes no
// order for the operands of `+`, and a take() evaluated ahead of the num()
// in one expression would count 0. The property's `new` was evaluated as a
// value and built no mailbox, and a bare `mb` in a method was resolved
// through the run's tables, which hold no object's, so put() placed
// nothing, get() stored nothing and y read x.
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
                      "    C c = new;\n"
                      "    c.give(4);\n"
                      "    n = c.mb.num();\n"
                      "    v = c.take();\n"
                      "    y = v * 10 + n;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            41u);
}

// §8.4 (printed page 181) with §15.4.1 (printed 374): each object's
// properties are its own, so two objects of the class hold two mailboxes,
// and what one is given the other does not hold: c1.take() retrieves the 1
// c1 was given and c2.take() the 2, 12. One mailbox shared by both would
// have handed c1's take() the 1 and c2's the 2 as well, 12 by luck of the
// order, so the second object is given first: c2.give(2) then c1.give(1)
// read 12 through two queues and 21 through one.
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
                      "    C c1 = new;\n"
                      "    C c2 = new;\n"
                      "    c2.give(2);\n"
                      "    c1.give(1);\n"
                      "    y = c1.take() * 10 + c2.take();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            12u);
}

// §8.11 with §15.4.1 (printed page 374): `this.mb` inside a method names the
// running object's mailbox as the bare name does, and `c.mb` from the module
// the object the handle refers to, so two puts through `this.mb.put(v)` are
// counted as 2 by `c.mb.num()` and the module's `c.mb.get(v)` retrieves the
// first, 24. Neither receiver was taken by the mailbox paths, which took an
// identifier alone, so num() answered nothing and get() stored nothing.
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
                      "    C c = new;\n"
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

// §15.4.3 (printed page 375) with §15.4.1 (printed 374): a property's
// `new(1)` bounds the object's queue to one message, so the class task's
// second put() waits where it stands until the module's `c.mb.get(got)` at
// time 5 makes room, and the fork branch that enabled the task records 5
// once it completes: got reads 1 and at 5, 15. A put() that did not wait
// would have recorded 0, and a queue built unbounded would have held both.
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

// §15.4.4 (printed page 375) with §15.4.1 (printed 374): try_put() on the
// object's bounded queue places its message while there is room and answers
// 1, and answers 0 once the queue holds the one message its `new(1)` bounds
// it to: 1 and 0 read as 10. A queue built unbounded, or none, would have
// read 11 or 0.
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
                      "    C c = new;\n"
                      "    y = c.fill();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

// §15.4.1 (printed page 374) with §8.7 (printed 184): a mailbox property may
// be built by a later `mb = new(1)` in a method rather than by its
// declaration, and a property declared with no initializer is the null
// handle until then. Built in the constructor, the queue takes one try_put()
// and refuses the second, 10; left to the generic store, the assignment
// wrote the carrier and both try_puts were served by no mailbox.
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
                      "    C c = new;\n"
                      "    y = c.fill();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

// §8.4 (printed page 181): a property declared `mailbox mb;` with no
// initializer holds the null handle, and a method called through it is
// illegal, reported at the call as a method of a user class called through
// a null handle is. Resolved by name alone, the put() was served by no
// mailbox and nothing was reported.
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
      "    C c = new;\n"
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

// The source of the typedef cases: `head` declares the typedef, and the
// class declares its mailbox property through the type `type` names, is
// given 4 and 5, counts 2 and takes the 4 back, 42.
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

// §15.4.9 (printed page 377) with §6.18 (printed 118) and §8.7 (printed
// 184): a class property declared through a typedef of `mailbox #(int)`,
// `mb_t mb = new`, is a mailbox as one declared `mailbox mb` is, built per
// object when the object is constructed, so give(4) and give(5) place two
// messages, num() counts 2 and take() retrieves the 4: 42. The run held no
// table of what a typedef stands for, so the property was of no type it
// knew: its `new` built no mailbox and its every method was called through
// a null handle.
TEST(MailboxSim, TypedefdMailboxPropertyIsBuiltPerObject) {
  EXPECT_EQ(RunAndGet(TypedefdMailboxPropertySrc(
                          "typedef mailbox #(int) mb_t;\n", "mb_t"),
                      "y"),
            42u);
}

// §15.4.9 (printed page 377) with §26.3 (printed 808): the typedef may be a
// package's, reached through the package scope resolution operator, so a
// property declared `p::mb_t mb = new` is the same mailbox, read as 42
// above. The name is recorded under "p::mb_t", which the bare name does not
// find.
TEST(MailboxSim, PackageTypedefdMailboxPropertyIsBuiltPerObject) {
  EXPECT_EQ(
      RunAndGet(TypedefdMailboxPropertySrc("package p;\n"
                                           "  typedef mailbox #(int) mb_t;\n"
                                           "endpackage\n",
                                           "p::mb_t"),
                "y"),
      42u);
}

// §6.18 (printed page 118) lets a typedef name stand for another typedef
// name, so a property declared through `typedef mb_t mb2_t` reaches the
// mailbox in two steps and reads 42 as above; a lookup that stopped at the
// first name found no mailbox.
TEST(MailboxSim, TypedefOfATypedefdMailboxPropertyIsBuiltPerObject) {
  EXPECT_EQ(
      RunAndGet(TypedefdMailboxPropertySrc("typedef mailbox #(int) mb_t;\n"
                                           "typedef mb_t mb2_t;\n",
                                           "mb2_t"),
                "y"),
      42u);
}

// §8.9 (printed page 186) with §15.4.1 (printed 374): a static mailbox
// property is one copy shared by every object of the class, created once,
// so what two objects' give() place lands in one queue: `C::mb.num()` from
// the module counts both, and `c2.mb.num()` through a handle counts the same
// queue, 22. Two queues would have counted 1 and 1, and the run's tables,
// which the static property was left to, held none, so put() placed nothing
// and `C::mb` named nothing.
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
                      "    C c1 = new;\n"
                      "    C c2 = new;\n"
                      "    c1.give(1);\n"
                      "    c2.give(2);\n"
                      "    y = C::mb.num() * 10 + c2.mb.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            22u);
}

// §8.10 (printed pages 186-187) with §8.9 (printed 186): a static method has
// no object and reaches the class's static properties, so its put() places
// into the one shared queue, which the module's `C::mb.get(v)` retrieves
// from in the order placed (§15.4.3) and `C::mb.num()` counts: 3 taken and
// 1 left, 31. Left to the run's tables, the static method's put() placed
// nothing and the get() waited on nothing.
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

// §15.4 (printed page 374) with §13.5.1 (printed 348) and §8.2 (printed
// 180): a mailbox variable is a handle to the mailbox object, and an object
// passed by value is passed as its handle, so a constructor's `mb = m` on a
// `mailbox m` formal makes the property a handle to the module's mailbox,
// and two objects built on it share the one queue (§8.12): c1.give(1) and
// c2.give(2) are counted 2 by the module's own `shared.num()`, and
// c1.take() retrieves the 1 placed first, 21. The assignment fell to the
// generic store, which wrote the handle's carrier, so the property stayed
// null and give() was reported as a call through a null handle.
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
                      "    C c1 = new(shared);\n"
                      "    C c2 = new(shared);\n"
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

// §8.12 (printed page 188) with §15.4.1 (printed 374): `c2.mb = c1.mb`
// assigns a handle, leaving one mailbox under two properties rather than
// copying it, so the two messages c2 gives are counted 2 by c1's queue as by
// c2's, 22. Two queues would have read 02, and the generic store, which the
// assignment fell to, wrote the carrier and left c2's own queue in place.
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
                      "    C c1 = new;\n"
                      "    C c2 = new;\n"
                      "    c2.mb = c1.mb;\n"
                      "    c2.give(5);\n"
                      "    c2.give(6);\n"
                      "    y = c1.mb.num() * 10 + c2.mb.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            22u);
}

// §8.7 (printed page 184) with §8.12 (printed 188): a property's declaration
// initializer may name a mailbox rather than construct one, `mailbox mb =
// shared;` in a class the module declares, and the property is then a handle
// to the module's mailbox: the object's two gives reach it, the module's
// `shared.get(v)` retrieves the 7 and num() counts the 8 left, 71. An
// initializer that was no `new` left the property null.
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
                      "    C c = new;\n"
                      "    c.give(7);\n"
                      "    c.give(8);\n"
                      "    shared.get(v);\n"
                      "    y = v * 10 + shared.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            71u);
}

// §13.5.1 (printed page 348) with §8.2 (printed 180): a `mailbox m` formal
// is a handle to the actual's mailbox, so a function's `m.put(v)` places
// into the module's queue: 9 and 8 placed, the 9 retrieved and the 8 left,
// 91. The formal was a carrier bound to no object, so its put() reached no
// mailbox.
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

// §8.23 (printed pages 200-201) with §8.9 (printed 186): a nested class's
// method reaches the containing class's static properties by their bare
// names, so Inner's give(4) places into Outer's one static mailbox, which
// the module's `Outer::mb.num()` counts as 1 and `Outer::mb.get(v)`
// retrieves the 4 from: 14. The bare name was looked for along Inner's base
// chain alone, which declares no mb, so the put() reached nothing and the
// count read 0.
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
                      "    Outer::Inner i = new;\n"
                      "    i.give(4);\n"
                      "    y = Outer::mb.num() * 10;\n"
                      "    Outer::mb.get(v);\n"
                      "    y = y + v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            14u);
}

// The source of the static-initialization cases: the package p declares
// `int K = 1`, the typedef `head` and a class whose static mailbox property,
// declared through the type `type` names, is built by `new(K)`; the module
// writes K to 3 and then tries to place two messages, reading the two
// try_put() results as a two-digit number.
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

// §8.9 (printed page 186) with §6.21 (printed 132-133) and §15.4.1 (printed
// 374): a static property's one copy is created at the class's static
// initialization, its `new(K)` reading K as it stands then, so the package
// class's mailbox is bounded by the package's `int K = 1` and the module's
// `K = 3` before the first put() does not widen it: the first try_put()
// reads 1 and the second, on the full mailbox, 0, 10. Built on the first
// reference instead, the `new` read the 3 and both reads were 1, 11.
TEST(MailboxSim, StaticMailboxPropertyIsBuiltAtStaticInitialization) {
  EXPECT_EQ(RunAndGet(StaticMailboxBoundedByKSrc("", "mailbox"), "y"), 10u);
}

// §6.18 (printed page 118) with §8.9 (printed 186) and §6.21 (printed
// 132-133): a typedef name stands for its type, so a static property
// declared `static mb_t mb = new(K)` through the package's `typedef mailbox
// mb_t` is the mailbox above, built at the class's static initialization
// with the bound K then holds, 1: the reads are 10 as above. The run's
// table of what a typedef stands for was filled after the package's class
// was lowered, so the static initialization knew the property for no
// mailbox and the first `C::mb.try_put(1)` built it, reading the 3, 11.
TEST(MailboxSim, StaticTypedefdMailboxPropertyIsBuiltAtStaticInitialization) {
  EXPECT_EQ(
      RunAndGet(StaticMailboxBoundedByKSrc("  typedef mailbox mb_t;\n", "mb_t"),
                "y"),
      10u);
}

}  // namespace
