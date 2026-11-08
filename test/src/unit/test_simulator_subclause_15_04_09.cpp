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
      "    static string msg = \"abc\";\n"
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

TEST(MailboxSim, StringMailboxPutPeekedAndGotReadsOneMessage) {
  ExpectStringMailboxPeekedThenTaken("    m.put(msg);\n", "    m.get(r);\n", 0);
}

TEST(MailboxSim, StringMailboxTryPutPeekedAndTryGotReadsOneMessage) {
  ExpectStringMailboxPeekedThenTaken("    i = m.try_put(msg) * 10;\n",
                                     "    i = i + m.try_get(r);\n", 11);
}

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

const char* const kModuleTypedefHead =
    "module t;\n"
    "  typedef mailbox #(string) s_mbox;\n"
    "  s_mbox sm = new;\n";

std::string PackageTypedefHead(const std::string& decl) {
  return "package p;\n"
         "  typedef mailbox #(string) s_mbox;\n"
         "endpackage\n"
         "module t;\n" +
         decl;
}

TEST(MailboxSim, TypedefdMailboxCarriesItsMessages) {
  ExpectMailboxCarriesHello(kModuleTypedefHead);
}

TEST(MailboxSim, PackageQualifiedTypedefdMailboxCarriesItsMessages) {
  ExpectMailboxCarriesHello(PackageTypedefHead("  p::s_mbox sm = new;\n"));
}

TEST(MailboxSim, TypedefOfAPackageQualifiedMailboxTypedefCarriesItsMessages) {
  ExpectMailboxCarriesHello(
      PackageTypedefHead("  typedef p::s_mbox my_mbox;\n"
                         "  my_mbox sm = new;\n"));
}

TEST(MailboxSim, TypedefdMailboxRejectsAGetOfAnotherType) {
  ExpectGetOfAnotherTypeReported(kModuleTypedefHead, 5);
}

TEST(MailboxSim, PackageQualifiedTypedefdMailboxRejectsAGetOfAnotherType) {
  ExpectGetOfAnotherTypeReported(PackageTypedefHead("  p::s_mbox sm = new;\n"),
                                 7);
}

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
         "    static C c = new;\n"
         "    c.go();\n"
         "  end\n"
         "endmodule\n";
}

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

TEST(MailboxSim, TypedefdMailboxPropertyRejectsAPutOfAnotherType) {
  ExpectPropertyCallReported(
      PropertyMailboxSrc(kPropertyTypedefHead, "mb_t", "    mb.put(\"s\");\n"),
      "put", 5);
}

TEST(MailboxSim, TypedefdMailboxPropertyRejectsAGetOfAnotherType) {
  ExpectPropertyCallReported(PropertyMailboxSrc(kPropertyTypedefHead, "mb_t",
                                                "    string s;\n"
                                                "    mb.put(1);\n"
                                                "    mb.get(s);\n"),
                             "get", 7);
}

TEST(MailboxSim, ParameterizedMailboxPropertyRejectsAPutOfAnotherType) {
  ExpectPropertyCallReported(
      PropertyMailboxSrc("", "mailbox #(int)", "    mb.put(\"s\");\n"), "put",
      4);
}

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
         "    static p::C c = new;\n"
         "    c.go();\n"
         "    y = c.mb.num();\n"
         "  end\n"
         "endmodule\n";
}

TEST(MailboxSim, PackageClassMailboxPropertyThroughThePackageOwnTypedef) {
  EXPECT_EQ(
      RunAndGet(PackageClassMailboxSrc("  typedef mailbox mb_t;\n", "mb_t"),
                "y"),
      1u);
}

TEST(MailboxSim, PackageClassMailboxPropertyThroughAChainOfPackageTypedefs) {
  EXPECT_EQ(RunAndGet(PackageClassMailboxSrc("  typedef mailbox mb_t;\n"
                                             "  typedef mb_t mb2_t;\n",
                                             "mb2_t"),
                      "y"),
            1u);
}

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

TEST(MailboxSim, PackageClassMailboxPropertyThroughOwnTypedefRejectsAPut) {
  ExpectPackagePropertyPutOfStringReported(kPackageIntMailboxTypedef, "mb_t",
                                           6);
}

TEST(MailboxSim, PackageClassMailboxPropertyThroughTypedefChainRejectsAPut) {
  ExpectPackagePropertyPutOfStringReported(
      std::string(kPackageIntMailboxTypedef) + "  typedef mb_t mb2_t;\n",
      "mb2_t", 7);
}

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
