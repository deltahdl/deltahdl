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

Logic4Snapshot Msg(uint64_t v) {
  Logic4Word word{v, 0};
  Logic4Vec vec{64, 1, &word};
  Logic4Snapshot snap;
  snap.Capture(vec);
  return snap;
}

uint64_t Word(const Logic4Snapshot& msg) { return msg.Get().ToUint64(); }

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

TEST(IpcSync, MailboxGetBlocksUntilMessagePlaced) {
  MailboxObject mb;
  std::vector<int> ran;
  Logic4Snapshot got;
  auto getter = SpawnGetter(mb, got, ran, 9);
  getter.h.resume();
  ASSERT_EQ(mb.get_waiters.size(), 1u);
  EXPECT_TRUE(ran.empty());

  EXPECT_EQ(mb.TryPut(Msg(0x55).Get()), 1);
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 9);
  EXPECT_TRUE(mb.get_waiters.empty());
  EXPECT_EQ(Word(got), 0x55u);
  EXPECT_EQ(mb.Num(), 0);

  getter.h.destroy();
}

TEST(IpcSync, MailboxWaitingQueuePreservesArrivalOrder) {
  MailboxObject mb;
  std::vector<int> ran;
  Logic4Snapshot got_first;
  Logic4Snapshot got_second;
  auto first = SpawnGetter(mb, got_first, ran, 1);
  auto second = SpawnGetter(mb, got_second, ran, 2);
  first.h.resume();
  second.h.resume();
  ASSERT_EQ(mb.get_waiters.size(), 2u);
  EXPECT_TRUE(ran.empty());

  EXPECT_EQ(mb.TryPut(Msg(0xAA).Get()), 1);
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 1);
  EXPECT_EQ(Word(got_first), 0xAAu);

  EXPECT_EQ(mb.TryPut(Msg(0xBB).Get()), 1);
  ASSERT_EQ(ran.size(), 2u);
  EXPECT_EQ(ran[1], 2);
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

constexpr MailboxMessageType kTypeInt =
    MailboxMessageType::Integral(32, true, MailboxMessageType::States::kTwo);
constexpr MailboxMessageType kTypeString = MailboxMessageType::String();

TEST(IpcSync, MailboxGetMaintainsTypePlacedByPut) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);
  Logic4Snapshot msg;
  EXPECT_EQ(mb.Get(msg, kTypeInt), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(msg), 0xABu);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxGetRetrievesEachMessageWithItsOwnStoredType) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);
  mb.TryPut(Msg(0xCD).Get(), kTypeString);
  Logic4Snapshot msg;

  EXPECT_EQ(mb.Get(msg, kTypeString), MbxGetStatus::kTypeError);
  EXPECT_EQ(mb.Num(), 2);

  EXPECT_EQ(mb.Get(msg, kTypeInt), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(msg), 0xABu);
  EXPECT_EQ(mb.Get(msg, kTypeString), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(msg), 0xCDu);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxGetTypeMismatchGeneratesError) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);
  Logic4Snapshot msg = Msg(0xEE);
  EXPECT_EQ(mb.Get(msg, kTypeString), MbxGetStatus::kTypeError);
  EXPECT_EQ(Word(msg), 0xEEu);
  EXPECT_EQ(mb.Num(), 1);
}

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
                      "    static c_t h = new;\n"
                      "    h.v = 5;\n"
                      "    mb.put(h);\n"
                      "    mb.get(g);\n"
                      "    r = g.v * 10 + mb.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            50u);
}

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
      "    static c_t h = new;\n"
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

TEST(MailboxSim, PutInsideAFunctionPlacesTheMessage) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  mailbox mb = new;\n"
                      "  int x, r;\n"
                      "  function void f();\n"
                      "    mb.put(8);\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    f();\n"
                      "    mb.get(x);\n"
                      "    r = x * 10 + mb.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            80u);
}

TEST(MailboxSim, PutInsideAFunctionOnAFullMailboxIsAnError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  mailbox mb = new(1);\n"
      "  int x, n;\n"
      "  function void f();\n"
      "    mb.put(8);\n"
      "    mb.put(9);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    f();\n"
      "    mb.get(x);\n"
      "    n = x * 10 + mb.num();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "mailbox put(): 'mb' is full, so the call would "
                            "block inside a function",
                            6, "13.4"));
  ExpectWord(f, "n", 80u);
}

TEST(MailboxSim, GetInAClassTaskResumesOnItsOwnObject) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class Cons;\n"
      "    int id, got;\n"
      "    mailbox mb;\n"
      "    function new(int i, mailbox m); id = i; mb = m; endfunction\n"
      "    task run();\n"
      "      int x;\n"
      "      mb.get(x);\n"
      "      got = this.id * 100 + x * 10 + ($time == 5) * 5;\n"
      "    endtask\n"
      "  endclass\n"
      "  mailbox mb = new;\n"
      "  Cons c;\n"
      "  int r;\n"
      "  initial begin\n"
      "    c = new(7, mb);\n"
      "    fork\n"
      "      c.run();\n"
      "      #5 mb.put(9);\n"
      "    join\n"
      "    r = c.got;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 795u);
}

TEST(MailboxSim, InterfaceMailboxGetReachedThroughTheInstance) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "interface chan;\n"
      "  mailbox mb = new;\n"
      "  task send(int x); mb.put(x); endtask\n"
      "endinterface\n"
      "module t;\n"
      "  chan c();\n"
      "  int v, r;\n"
      "  initial fork\n"
      "    begin c.mb.get(v); r = v * 10 + $time; end\n"
      "    #3 c.send(21);\n"
      "  join\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 213u);
}

TEST(MailboxSim, GetStoresIntoAPropertyAQueueElementAndAnArrayElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C; int x; endclass\n"
      "  mailbox mb = new;\n"
      "  C c; int q[$]; int arr[2]; int r;\n"
      "  initial begin\n"
      "    c = new; q.push_back(0);\n"
      "    mb.put(3); mb.put(4); mb.put(5);\n"
      "    mb.get(c.x); mb.get(q[0]); mb.get(arr[1]);\n"
      "    r = c.x * 100 + q[0] * 10 + arr[1];\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 345u);
}

}  // namespace
