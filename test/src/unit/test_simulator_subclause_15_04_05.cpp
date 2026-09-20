#include <gtest/gtest.h>

#include <coroutine>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

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

// Minimal getter coroutine used to observe the get-side wakeup. It starts
// suspended; the first resume runs it to the co_await, where — while the
// mailbox is empty — the awaiter parks the handle on the mailbox's get-waiter
// queue. A later put() that places a message resumes it through production
// WakeGetWaiters(), at which point it retrieves the message and records that it
// ran. Parking on get_waiters is exactly what a get awaiter's suspend does; the
// rule under observation here is the resume performed by WakeGetWaiters().
struct GetWaiter {
  MailboxObject& mbx;
  bool await_ready() { return !mbx.messages.empty(); }
  void await_suspend(std::coroutine_handle<> h) {
    mbx.get_waiters.push_back(h);
  }
  void await_resume() const noexcept {}
};

struct BlockingGetter {
  struct promise_type {
    BlockingGetter get_return_object() {
      return BlockingGetter{
          std::coroutine_handle<promise_type>::from_promise(*this)};
    }
    std::suspend_always initial_suspend() noexcept { return {}; }
    std::suspend_always final_suspend() noexcept { return {}; }
    void return_void() {}
    void unhandled_exception() {}
  };
  std::coroutine_handle<promise_type> h;
};

inline BlockingGetter SpawnGetter(MailboxObject& mbx, Logic4Snapshot& out,
                                  std::vector<int>& ran, int id) {
  co_await GetWaiter{mbx};
  mbx.Get(out);
  ran.push_back(id);
}

TEST(IpcSync, MailboxGetRetrievesFrontMessage) {
  MailboxObject mb;
  mb.TryPut(Msg(10).Get());
  mb.TryPut(Msg(20).Get());
  Logic4Snapshot msg;
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(msg), 10u);
  EXPECT_EQ(mb.Num(), 1);
}

TEST(IpcSync, MailboxGetEmptyReturnsBlock) {
  MailboxObject mb;
  Logic4Snapshot msg;
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kBlock);
  EXPECT_EQ(mb.Num(), 0);
}

// §15.4.5: a get() on an empty mailbox blocks the current process until a
// message is placed in the mailbox. The getter parks while the mailbox is empty
// and is resumed only once a put() supplies a message, after which it retrieves
// that message.
TEST(IpcSync, MailboxGetBlocksUntilMessagePlaced) {
  MailboxObject mb;  // empty
  std::vector<int> ran;
  Logic4Snapshot got;
  auto getter = SpawnGetter(mb, got, ran, 9);
  getter.h.resume();  // runs to the co_await; empty -> parks on get_waiters
  ASSERT_EQ(mb.get_waiters.size(), 1u);
  EXPECT_TRUE(ran.empty());

  // Placing a message wakes the parked getter via WakeGetWaiters().
  EXPECT_EQ(mb.TryPut(Msg(0x55).Get()), 1);
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 9);
  EXPECT_TRUE(mb.get_waiters.empty());
  // The resumed getter retrieved the placed message and consumed it.
  EXPECT_EQ(Word(got), 0x55u);
  EXPECT_EQ(mb.Num(), 0);

  getter.h.destroy();
}

// §15.4.5: the mailbox waiting queue is FIFO — the arrival order of processes
// blocked in get() shall be preserved. Two getters park on an empty mailbox in
// arrival order; each subsequent put() wakes the earliest-arrived waiter first,
// so the first getter retrieves the first placed message and the second getter
// the second. This observes production WakeGetWaiters() servicing get_waiters
// from the front.
TEST(IpcSync, MailboxWaitingQueuePreservesArrivalOrder) {
  MailboxObject mb;  // empty
  std::vector<int> ran;
  Logic4Snapshot got_first;
  Logic4Snapshot got_second;
  auto first = SpawnGetter(mb, got_first, ran, 1);
  auto second = SpawnGetter(mb, got_second, ran, 2);
  first.h.resume();   // parks first on get_waiters
  second.h.resume();  // parks second behind it
  ASSERT_EQ(mb.get_waiters.size(), 2u);
  EXPECT_TRUE(ran.empty());

  // Each placed message wakes exactly the head of the waiting queue.
  EXPECT_EQ(mb.TryPut(Msg(0xAA).Get()), 1);
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 1);  // the earliest arrival ran first
  EXPECT_EQ(Word(got_first), 0xAAu);

  EXPECT_EQ(mb.TryPut(Msg(0xBB).Get()), 1);
  ASSERT_EQ(ran.size(), 2u);
  EXPECT_EQ(ran[1], 2);  // the later arrival ran second
  EXPECT_EQ(Word(got_second), 0xBBu);
  EXPECT_TRUE(mb.get_waiters.empty());

  first.h.destroy();
  second.h.destroy();
}

TEST(IpcSync, MailboxGetFifoOrder) {
  MailboxObject mb;
  mb.TryPut(Msg(100).Get());
  mb.TryPut(Msg(200).Get());
  mb.TryPut(Msg(300).Get());
  Logic4Snapshot msg;
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(msg), 100u);
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(msg), 200u);
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(msg), 300u);
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kBlock);
}

TEST(IpcSync, MailboxGetFreesSpaceForPut) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.TryPut(Msg(10).Get()), 1);
  EXPECT_EQ(mb.TryPut(Msg(20).Get()), 0);
  Logic4Snapshot msg;
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(msg), 10u);
  EXPECT_EQ(mb.TryPut(Msg(30).Get()), 1);
  EXPECT_EQ(mb.Num(), 1);
}

// Two non-equivalent message types, §6.22.2 c)'s int and §6.22.1 a)'s string.
constexpr MailboxMessageType kTypeInt =
    MailboxMessageType::Integral(32, true, MailboxMessageType::States::kTwo);
constexpr MailboxMessageType kTypeString = MailboxMessageType::String();

// §15.4.5: the mailbox maintains the data type placed by put(), so a get()
// whose variable type matches that stored type retrieves the value.
TEST(IpcSync, MailboxGetMaintainsTypePlacedByPut) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);
  Logic4Snapshot msg;
  EXPECT_EQ(mb.Get(msg, kTypeInt), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(msg), 0xABu);
  EXPECT_EQ(mb.Num(), 0);
}

// §15.4.5: a single (typeless) mailbox can carry messages of different types,
// and the implementation maintains the type placed by each put() individually.
// Two messages with distinct stored types coexist in the queue; each get()
// checks the type of the specific (front) message it retrieves, so a get()
// whose variable type matches the front message succeeds while the other stored
// type waits its turn and is then retrieved by a get() of its own matching
// type.
TEST(IpcSync, MailboxGetRetrievesEachMessageWithItsOwnStoredType) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);     // first placed, first out
  mb.TryPut(Msg(0xCD).Get(), kTypeString);  // second placed, second out
  Logic4Snapshot msg;

  // The front message was placed as kTypeInt: a kTypeString get() sees the
  // front's maintained type, not the later kTypeString message, and errors.
  EXPECT_EQ(mb.Get(msg, kTypeString), MbxGetStatus::kTypeError);
  EXPECT_EQ(mb.Num(), 2);

  // Retrieved by its own stored type; the queue then advances to the second.
  EXPECT_EQ(mb.Get(msg, kTypeInt), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(msg), 0xABu);
  EXPECT_EQ(mb.Get(msg, kTypeString), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(msg), 0xCDu);
  EXPECT_EQ(mb.Num(), 0);
}

// §15.4.5: when the variable type is not equivalent to the stored message type,
// a run-time type error is generated instead of a retrieval.
TEST(IpcSync, MailboxGetTypeMismatchGeneratesError) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);
  Logic4Snapshot msg = Msg(0xEE);
  EXPECT_EQ(mb.Get(msg, kTypeString), MbxGetStatus::kTypeError);
  // The errored get() does not consume the message and does not clobber msg.
  EXPECT_EQ(Word(msg), 0xEEu);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.5 (printed pages 375-376): get() on an empty mailbox blocks the
// process until a message is placed in the mailbox, and then removes that
// message. The put() at time 3 is what ends the wait, so the value 8 reaches
// v at time 3: 8 and the time test read as 81. A get() that did not wait
// would have stored nothing and read the time as 0.
TEST(MailboxSim, GetWaitsUntilAMessageIsPlaced) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  int v, r;\n"
      "  initial begin\n"
      "    mb.get(v);\n"
      "    r = v * 10 + ($time == 3);\n"
      "  end\n"
      "  initial #3 mb.put(8);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 81u);
}

// §15.4 (printed page 374) with §15.4.3 (printed 375): a message is any
// singular expression, so a 96-bit vector travels through the mailbox whole
// and get() hands all of it back: the two words of v read the three 32-bit
// pieces the literal was written from. Held as one 64-bit word, the message
// lost 32'h01234567, the upper piece, and v's second word read 0.
TEST(MailboxSim, GetHandsBackAWideMessageWhole) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  logic [95:0] w = 96'h01234567_89ABCDEF_00112233;\n"
      "  logic [95:0] v;\n"
      "  initial begin\n"
      "    mb.put(w);\n"
      "    mb.get(v);\n"
      "  end\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.width, 96u);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[0].aval, 0x89ABCDEF00112233u);
  EXPECT_EQ(var->value.words[1].aval, 0x01234567u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
  EXPECT_EQ(var->value.words[1].bval, 0u);
}

// §15.4 (printed page 374): a 4-state message keeps its x and z bits through
// the mailbox, so the variable get() fills reads case-equal to the value
// put() placed: 1 and a num() of 0 read as 10. Held as a 64-bit word, the
// unknown bits were dropped and the case equality read 0.
TEST(MailboxSim, GetHandsBackAFourStateMessageWhole) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  logic [7:0] a = 8'b1x0z_0101;\n"
      "  logic [7:0] b;\n"
      "  int r;\n"
      "  initial begin\n"
      "    mb.put(a);\n"
      "    mb.get(b);\n"
      "    r = (b === 8'b1x0z_0101) * 10 + mb.num();\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.words[0].aval & 0xFFu, 0xC5u);
  EXPECT_EQ(b->value.words[0].bval & 0xFFu, 0x50u);
}

// §15.4.9 (printed page 377) with §15.4.5: the subclause's own example puts
// "hello" into a `mailbox #(string)` and get() leaves the string variable
// holding "hello". Held as a 64-bit word, the message carried the characters
// but the store sized them to the variable and a string read back cut.
TEST(MailboxSim, GetHandsBackAStringMessageWhole) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox #(string) sm = new;\n"
      "  string s;\n"
      "  initial begin\n"
      "    sm.put(\"hello\");\n"
      "    sm.get(s);\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(VecToStr(var->value), "hello");
}

// §15.4.5's run-time error, reported at the variable get() named, spelled
// as `target`, on line `line`; and the value a variable was left holding.
void ExpectGetTypeError(const SimFixture& f, const std::string& target,
                        uint32_t line) {
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "mailbox get(): the message's type is not "
                            "equivalent to the type of '" +
                                target + "'",
                            line, "15.4.5"));
}

void ExpectWord(SimFixture& f, std::string_view name, uint64_t expected) {
  auto* var = f.ctx.FindVariable(name);
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), expected);
}

void ExpectString(SimFixture& f, std::string_view name,
                  const std::string& expected) {
  auto* var = f.ctx.FindVariable(name);
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(VecToStr(var->value), expected);
}

// §15.4.5 (printed page 376): when the type of the message variable is not
// equivalent to the type of the message in the mailbox, a run-time error is
// generated. The typeless mailbox holds the int 7, and get() into a string
// is reported at the variable, leaves the message in the queue and the
// string as it was: "keep" and a num() of 1. An untyped retrieval stored
// the 7 over the string and answered 0 for num().
TEST(MailboxSim, GetIntoAVariableOfAnotherTypeIsAnError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  string s = \"keep\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    mb.put(7);\n"
      "    mb.get(s);\n"
      "    n = mb.num();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ExpectGetTypeError(f, "s", 7);
  ExpectString(f, "s", "keep");
  ExpectWord(f, "n", 1u);
}

// §15.4.3 (printed page 375) has put() place any singular expression, and
// §15.4.5 (printed 376) has the mailbox maintain the data type it was placed
// with: `a + 1` over the int a is, by §11.6.1 and §11.8.1, a 32-bit signed
// integral, so get() into a string is the run-time error, reported at the
// string with the message left in the queue and the string as it was, and
// get() into an int then reads the sum: 5 and a num() of 0 read as 50. A
// computed actual placed with no type stored the 5 over the string and
// raised nothing, the int get() then waiting on an empty mailbox.
TEST(MailboxSim, PutOfAComputedActualCarriesTheSumsType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  int a = 4, b, n;\n"
      "  string s = \"keep\";\n"
      "  initial begin\n"
      "    mb.put(a + 1);\n"
      "    mb.get(s);\n"
      "    mb.get(b);\n"
      "    n = b * 10 + mb.num();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ExpectGetTypeError(f, "s", 7);
  ExpectString(f, "s", "keep");
  ExpectWord(f, "n", 50u);
}

// §15.4.5 (printed page 376) with §7.2.1: the message variable may be any
// valid left-hand expression, and a member of a structure is of the type its
// declaration gives it. The int 7 is not equivalent to the 8-bit byte member
// (§6.22.2 c) asks for one total width), so `mb.get(s.b)` is the run-time
// error, reported at the member with 9 left in it, and `mb.get(s.i)` into the
// int member reads the 7: 9, 7 and a num() of 0 read as 970. A member with
// no type read stored the 7 in the byte, and the int member's get() then
// waited on an empty mailbox, leaving n at 0.
TEST(MailboxSim, GetIntoAMemberOfAnotherTypeIsAnError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  typedef struct packed { byte b; int i; } s_t;\n"
      "  s_t s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.b = 9;\n"
      "    mb.put(7);\n"
      "    mb.get(s.b);\n"
      "    mb.get(s.i);\n"
      "    n = s.b * 100 + s.i * 10 + mb.num();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ExpectGetTypeError(f, "s.b", 9);
  ExpectWord(f, "n", 970u);
}

// §15.4.5 (printed page 376) with §7.4.2: an element of an unpacked array is
// of the array's element type, the signed 8-bit byte. The int 6 is not
// equivalent to it, so `mb.get(arr[i])` is the run-time error and the int w
// takes the 6; the literal 8'sd3 is 8 bits and signed, so the element then
// reads it, where the unsigned 8'd3 would not have (§6.22.2 c) asks for one
// signedness): 6, 3 and a num() of 0 read as 630. An element with no type
// read stored the 6, and the int's get() then waited on an empty mailbox.
TEST(MailboxSim, GetIntoAnElementOfAnotherTypeIsAnError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  byte arr[2];\n"
      "  int i = 1, w, n;\n"
      "  initial begin\n"
      "    mb.put(6);\n"
      "    mb.get(arr[i]);\n"
      "    mb.get(w);\n"
      "    mb.put(8'sd3);\n"
      "    mb.get(arr[i]);\n"
      "    n = w * 100 + arr[1] * 10 + mb.num();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ExpectGetTypeError(f, "arr[i]", 7);
  ExpectWord(f, "n", 630u);
}

// §6.22.1 b) and d) (printed page 135) with §6.22.2 a) (printed 136): a
// typedef that renames a class matches the class, so a handle declared
// through it is of a type equivalent to one declared by the class name, and
// §15.4.5 (printed 376) hands the message to get(). The block-local `c_t h`
// holding v = 5 is put and the `C g` get() takes it: 5 and a num() of 0 read
// as 50. Typed by the typedef's name, the get() was reported not equivalent
// and g stayed null.
TEST(MailboxSim, GetIntoAHandleOfTheClassTakesATypedefdHandlesMessage) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int v;\n"
                      "endclass\n"
                      "module t;\n"
                      "  typedef C c_t;\n"
                      "  mailbox mb = new;\n"
                      "  C g;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    c_t h = new;\n"
                      "    h.v = 5;\n"
                      "    mb.put(h);\n"
                      "    mb.get(g);\n"
                      "    r = g.v * 10 + mb.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            50u);
}

// §6.22.1 d) (printed page 135): a typedef for a class matches the class it
// renames and no other, so a `d_t k` declared through a typedef of D is not
// equivalent to the C handle in the queue, and §15.4.5 (printed 376) makes
// its get() the run-time error, reported at k with the message left in the
// queue: a num() of 1. A typedef resolved to any class at all would have
// stored the C handle in k and answered 0.
TEST(MailboxSim, GetIntoAHandleOfAnotherTypedefdClassIsAnError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int v;\n"
      "endclass\n"
      "class D;\n"
      "  int w;\n"
      "endclass\n"
      "module t;\n"
      "  typedef C c_t;\n"
      "  typedef D d_t;\n"
      "  mailbox mb = new;\n"
      "  int n;\n"
      "  initial begin\n"
      "    c_t h = new;\n"
      "    d_t k;\n"
      "    mb.put(h);\n"
      "    mb.get(k);\n"
      "    n = mb.num();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ExpectGetTypeError(f, "k", 16);
  ExpectWord(f, "n", 1u);
}

// §15.4.3 (printed page 375) has put() place an object handle, and §15.3
// makes a semaphore a built-in class of which the run keeps no class record,
// so its handle is a message of the class named by the declaration and not
// of any type: §15.4.5 (printed 376) makes get() into an int the run-time
// error, reported at n with n as it was and the message left in the queue:
// 4 and a num() of 1. A handle of an unrecorded class typed as any would
// have stored the handle over the 4 and answered 0.
TEST(MailboxSim, GetOfABuiltInClassHandleIntoAnIntIsAnError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  semaphore s = new(1);\n"
      "  int n = 4, k;\n"
      "  initial begin\n"
      "    mb.put(s);\n"
      "    mb.get(n);\n"
      "    k = mb.num();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ExpectGetTypeError(f, "n", 7);
  ExpectWord(f, "n", 4u);
  ExpectWord(f, "k", 1u);
}

// §7.2.1 (printed page 147) gives each member of a packed structure its
// declared type, and §6.22.2 c) (printed 136) has two integral types
// equivalent at one total width, one signedness and one number of states:
// the member `logic signed [7:0] m` is 8 bits and signed, so §15.4.5
// (printed 376) hands it the literal 8'sd3, which is both: 3 and a num() of
// 0 read as 30. Typed by its kind alone, the member read unsigned, the get()
// was reported not equivalent and r stayed 0.
TEST(MailboxSim, GetIntoASignedLogicMemberTakesASignedMessage) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  mailbox mb = new;\n"
                      "  struct packed { logic signed [7:0] m; int i; } s;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    mb.put(8'sd3);\n"
                      "    mb.get(s.m);\n"
                      "    r = s.m * 10 + mb.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            30u);
}

// §6.22.2 c) (printed page 136): the unsigned 8'd3 is of the member's width
// but not of its signedness, so `mb.get(s.m)` into the `logic signed [7:0]`
// member is §15.4.5's run-time error (printed 376), reported at the member
// with the message left in the queue and the member as it was: 5 and a
// num() of 1 read as 51. The member typed unsigned took the 3 and read 30.
TEST(MailboxSim, GetIntoASignedLogicMemberRefusesAnUnsignedMessage) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  struct packed { logic signed [7:0] m; int i; } s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.m = 5;\n"
      "    mb.put(8'd3);\n"
      "    mb.get(s.m);\n"
      "    n = s.m * 10 + mb.num();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ExpectGetTypeError(f, "s.m", 8);
  ExpectWord(f, "n", 51u);
}

}  // namespace
