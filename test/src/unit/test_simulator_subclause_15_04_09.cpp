#include <gtest/gtest.h>

#include <cstdint>
#include <string>

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

// Runs a module whose `mailbox #(string) m` is declared at module scope and
// created by `m = new()` inside the initial, where the message "abc" is a
// local with an initializer; `place` puts it and `take` gets it into `r`
// after peek() has read it into `r_peek`, n counts the queue between the
// two, and i holds what the two calls answered where they answer anything.
// Reads "abc" from both strings, 1 from n and `want_i` from i. This is the
// shape of the suite's 15.4--mailbox-blocking.sv and
// 15.4--mailbox-non-blocking.sv (#2918), which differ only in the two calls.
void ExpectStringMailboxPeekedThenTaken(const std::string& place,
                                        const std::string& take,
                                        uint64_t want_i) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox #(string) m;\n"
      "  string r, r_peek;\n"
      "  int n, i;\n"
      "  initial begin\n"
      "    string msg = \"abc\";\n"
      "    m = new();\n" +
          place +
          "    m.peek(r_peek);\n"
          "    n = m.num();\n" +
          take + "  end\nendmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(VecToStr(var->value), "abc");
  auto* peeked = f.ctx.FindVariable("r_peek");
  ASSERT_NE(peeked, nullptr);
  EXPECT_EQ(VecToStr(peeked->value), "abc");
  auto* n = f.ctx.FindVariable("n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 1u);
  auto* i = f.ctx.FindVariable("i");
  ASSERT_NE(i, nullptr);
  EXPECT_EQ(i->value.ToUint64(), want_i);
}

// §15.4.9 (printed page 377) with §15.4.3, §15.4.7 and §15.4.5: put() on a
// string mailbox created in the initial places "abc", peek() copies it
// without removing it, so num() counts 1, and get() then hands the same
// "abc" to r; neither call answers anything, so i stays 0. The suite's
// 15.4--mailbox-blocking.sv: run 30725357212 reported it failing and no
// case here peeked a string message.
TEST(MailboxSim, StringMailboxPutPeekedAndGotReadsOneMessage) {
  ExpectStringMailboxPeekedThenTaken("    m.put(msg);\n", "    m.get(r);\n", 0);
}

// §15.4.9 (printed page 377) with §15.4.4 and §15.4.6: try_put() on the
// same mailbox places "abc" and answers 1, and after peek() has copied it
// and num() counted 1, try_get() takes it into r and answers 1 too, i
// holding 11 for the two. The suite's 15.4--mailbox-non-blocking.sv,
// reported failing by the same run.
TEST(MailboxSim, StringMailboxTryPutPeekedAndTryGotReadsOneMessage) {
  ExpectStringMailboxPeekedThenTaken("    i = m.try_put(msg) * 10;\n",
                                     "    i = i + m.try_get(r);\n", 11);
}

// Runs the source `head` -- a package, where the case has one, and a module
// `t` open with its string mailbox `sm` declared -- with a body that puts
// "hello", counts the queue by num() into `n` and gets the message into `s`,
// and reads "hello" from `s` and 1 from `n`. The declaration of `sm` is what
// each case below varies.
void ExpectMailboxCarriesHello(const std::string& head) {
  SimFixture f;
  auto* var = RunAndFindVar(head +
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

// Elaborates the source `head`, shaped as above, with a body whose get()
// reads the string mailbox `sm` into an int on the line `line`, and expects
// the §15.4.9 report there.
void ExpectGetOfAnotherTypeReported(const std::string& head, int line) {
  SimFixture f;
  ElaborateSrc(head +
                   "  int n;\n"
                   "  initial sm.get(n);\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "argument to mailbox method 'get' is not type-equivalent",
                    line, "15.4.9"));
}

// The head of the cases whose module declares the typedef itself.
const char* const kModuleTypedefHead =
    "module t;\n"
    "  typedef mailbox #(string) s_mbox;\n"
    "  s_mbox sm = new;\n";

// The head of the cases that reach the typedef through `p::`: the package
// holding it, and a module `t` whose mailbox declaration `decl` names it.
std::string PackageTypedefHead(const std::string& decl) {
  return "package p;\n"
         "  typedef mailbox #(string) s_mbox;\n"
         "endpackage\n"
         "module t;\n" +
         decl;
}

// §15.4.9 (printed page 377): the subclause's own form declares the
// parameterized mailbox through a typedef, `typedef mailbox #(string)
// s_mbox; s_mbox sm = new;`, and §6.18 makes the typedef name stand for the
// type it renames, so the declaration creates the mailbox as `mailbox
// #(string) sm = new` does: put("hello") is counted by num() as 1 and get()
// leaves s holding "hello". A declaration the typedef name left uncreated
// put on no queue, counted 0 and left s empty.
TEST(MailboxSim, TypedefdMailboxCarriesItsMessages) {
  ExpectMailboxCarriesHello(kModuleTypedefHead);
}

// §15.4.9 (printed page 377) with §26.3 (printed 808): the typedef of
// `mailbox #(string)` declared in a package is reached through the package
// scope resolution operator, so `p::s_mbox sm = new` creates the mailbox
// the module-scope typedef above does, carrying "hello" and counting 1. The
// typedef was looked up by its bare name, which the table holds only under
// "p::s_mbox", so the declaration created no queue: put() and get() ran on
// nothing, n counted 0 and s stayed empty.
TEST(MailboxSim, PackageQualifiedTypedefdMailboxCarriesItsMessages) {
  ExpectMailboxCarriesHello(PackageTypedefHead("  p::s_mbox sm = new;\n"));
}

// §6.18 (printed page 118) lets a typedef name stand for a type that is
// itself a typedef name, and §26.3 lets that name be a package's, so
// `typedef p::s_mbox my_mbox; my_mbox sm = new` reaches `mailbox #(string)`
// in two steps, one of them across the package qualifier: "hello" and 1 as
// above. A walk that stopped at the first name found `p::s_mbox` no class
// and created nothing.
TEST(MailboxSim, TypedefOfAPackageQualifiedMailboxTypedefCarriesItsMessages) {
  ExpectMailboxCarriesHello(
      PackageTypedefHead("  typedef p::s_mbox my_mbox;\n"
                         "  my_mbox sm = new;\n"));
}

// §15.4.9 (printed page 377): a mailbox declared through a typedef of
// `mailbox #(string)` is the parameterized mailbox, whose transfer methods
// the compiler verifies, so get() into an int is reported at the call under
// this subclause rather than left to the run.
TEST(MailboxSim, TypedefdMailboxRejectsAGetOfAnotherType) {
  ExpectGetOfAnotherTypeReported(kModuleTypedefHead, 5);
}

// §15.4.9 (printed page 377) with §26.3 (printed 808): the mailbox declared
// through the package's typedef, `p::s_mbox sm = new`, is the same
// parameterized mailbox, so its get() into an int earns the same report at
// the call, line 7 after the package's three lines. A declaration the
// qualified lookup missed was no mailbox to the check and its get() went
// unreported.
TEST(MailboxSim, PackageQualifiedTypedefdMailboxRejectsAGetOfAnotherType) {
  ExpectGetOfAnotherTypeReported(PackageTypedefHead("  p::s_mbox sm = new;\n"),
                                 7);
}

// The source of the class property cases: `head` declares a typedef or
// nothing, and the class declares its mailbox property `mb` through the
// type `type` names and a method `go()` whose body is `body`, which the
// module calls on a constructed object.
std::string PropertyMailboxSrc(const std::string& head, const std::string& type,
                               const std::string& body) {
  return head + "class C;\n  " + type +
         " mb = new;\n"
         "  function void go();\n" +
         body +
         "  endfunction\n"
         "endclass\n"
         "module t;\n"
         "  initial begin\n"
         "    C c = new;\n"
         "    c.go();\n"
         "  end\n"
         "endmodule\n";
}

// Runs `src` and expects the §15.4.9 report for the mailbox method
// `method` at the line `line`.
void ExpectPropertyCallReported(const std::string& src,
                                const std::string& method, int line) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to mailbox method '" + method + "' is not type-equivalent",
      line, "15.4.9"));
}

const char* const kPropertyTypedefHead = "typedef mailbox #(int) mb_t;\n";

// §15.4.9 (printed page 377) with §6.18 (printed 118): a class property
// declared through a typedef of `mailbox #(int)` is the parameterized
// mailbox, which accepts messages of its element type alone, so the
// method's put() of a string is reported at the call, as a module
// variable's is above. The property's own declaration carries no `#(T)`,
// so the run took the mailbox for a typeless one and the put() went
// unreported.
TEST(MailboxSim, TypedefdMailboxPropertyRejectsAPutOfAnotherType) {
  ExpectPropertyCallReported(
      PropertyMailboxSrc(kPropertyTypedefHead, "mb_t", "    mb.put(\"s\");\n"),
      "put", 5);
}

// §15.4.9 (printed page 377) with §15.4.5 (printed 375): the parameterized
// mailbox reached through the typedef hands its messages to a variable of
// its element type alone, so get() into a string is reported at the call
// under this subclause, as the module variable's is above, the 1 placed
// before it left in the queue. Taken for a typeless mailbox, the get()
// was left to the run's check, which reports under §15.4.5 and not here.
TEST(MailboxSim, TypedefdMailboxPropertyRejectsAGetOfAnotherType) {
  ExpectPropertyCallReported(PropertyMailboxSrc(kPropertyTypedefHead, "mb_t",
                                                "    string s;\n"
                                                "    mb.put(1);\n"
                                                "    mb.get(s);\n"),
                             "get", 7);
}

// §15.4.9 (printed page 377): the property declared `mailbox #(int) mb`
// outright is the same parameterized mailbox, so its put() of a string is
// reported at the call as the typedef'd one's is. The elaborator's check
// walks a module's items and never a class's methods, so the call was
// verified by nothing.
TEST(MailboxSim, ParameterizedMailboxPropertyRejectsAPutOfAnotherType) {
  ExpectPropertyCallReported(
      PropertyMailboxSrc("", "mailbox #(int)", "    mb.put(\"s\");\n"), "put",
      4);
}

// The source of the package class cases: the package `p` declares the
// typedef items `typedefs`, then a class C whose mailbox property `mb` is
// declared `new` through the type `type` names and whose go() puts the
// message `msg` into it; a module that imports nothing constructs a `p::C`,
// calls go() and counts the queue into y.
std::string PackageClassMailboxSrc(const std::string& typedefs,
                                   const std::string& type,
                                   const std::string& msg = "1") {
  return "package p;\n" + typedefs +
         "  class C;\n"
         "    " +
         type +
         " mb = new;\n"
         "    function void go();\n"
         "      mb.put(" +
         msg +
         ");\n"
         "    endfunction\n"
         "  endclass\n"
         "endpackage\n"
         "module top;\n"
         "  int y;\n"
         "  initial begin\n"
         "    p::C c = new;\n"
         "    c.go();\n"
         "    y = c.mb.num();\n"
         "  end\n"
         "endmodule\n";
}

// §26.2 (printed page 808) makes a package's declarations visible by their
// bare names throughout the package, its classes included, and §6.18
// (printed 118) makes the typedef name stand for the type it renames, so
// `mb_t mb = new` inside p's own class, with no module importing p, builds
// the mailbox `mailbox mb = new` builds: go()'s put(1) is counted by
// c.mb.num() as 1. The run keys the package's typedef "p::mb_t" and a
// module's `import p::*` is what adds the bare key, so with no import the
// bare name the class wrote found nothing, the property was a plain 32-bit
// value, the put() reached no queue and y read 0.
TEST(MailboxSim, PackageClassMailboxPropertyThroughThePackageOwnTypedef) {
  EXPECT_EQ(
      RunAndGet(PackageClassMailboxSrc("  typedef mailbox mb_t;\n", "mb_t"),
                "y"),
      1u);
}

// §6.18 (printed page 118) with §26.2 (printed 808): a package's typedef
// may stand for another of the package's typedefs, each written bare, so
// `typedef mb_t mb2_t` reaches the mailbox in two steps inside the package
// and the property reads 1 as above. Qualified at the first step alone, the
// chain's second name, the bare `mb_t` the target records, found nothing.
TEST(MailboxSim, PackageClassMailboxPropertyThroughAChainOfPackageTypedefs) {
  EXPECT_EQ(RunAndGet(PackageClassMailboxSrc("  typedef mailbox mb_t;\n"
                                             "  typedef mb_t mb2_t;\n",
                                             "mb2_t"),
                      "y"),
            1u);
}

// Runs the package class source whose go() puts the string "s" into the
// property declared through `type` from the package's `typedefs`, expects
// the §15.4.9 report for the put at the line `line`, and reads 0 from y,
// the rejected message placed on no queue.
void ExpectPackagePropertyPutOfStringReported(const std::string& typedefs,
                                              const std::string& type,
                                              int line) {
  SimFixture f;
  auto* var =
      RunAndFindVar(PackageClassMailboxSrc(typedefs, type, "\"s\""), f, "y");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "argument to mailbox method 'put' is not type-equivalent",
                    line, "15.4.9"));
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

const char* const kPackageIntMailboxTypedef =
    "  typedef mailbox #(int) mb_t;\n";

// §15.4.9 (printed page 377) with §26.2 (printed 808): the property of p's
// own class declared `mb_t mb = new` through the package's `typedef mailbox
// #(int) mb_t`, with no module importing p, is the parameterized mailbox of
// int, whose put() of a string is reported at the call, line 6, the message
// placed on no queue and y counting 0. The parameter list was read through
// the typedef chain by the bare name, which the run keys "p::mb_t", so the
// property was taken for a typeless mailbox and the put() went unreported.
TEST(MailboxSim, PackageClassMailboxPropertyThroughOwnTypedefRejectsAPut) {
  ExpectPackagePropertyPutOfStringReported(kPackageIntMailboxTypedef, "mb_t",
                                           6);
}

// §6.18 (printed page 118) with §26.2 (printed 808): the package's `typedef
// mb_t mb2_t` stands for its `mailbox #(int)` in two bare steps, so the
// property declared `mb2_t` earns the same report at the put, line 7 after
// the second typedef. Qualified at the first step alone, the chain's bare
// `mb_t` found no declaration and the put() went unreported.
TEST(MailboxSim, PackageClassMailboxPropertyThroughTypedefChainRejectsAPut) {
  ExpectPackagePropertyPutOfStringReported(
      std::string(kPackageIntMailboxTypedef) + "  typedef mb_t mb2_t;\n",
      "mb2_t", 7);
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
