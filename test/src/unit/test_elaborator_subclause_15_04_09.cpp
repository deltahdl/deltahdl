#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(MailboxParameterizedElaborator, ParameterizedIntDeclaration) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].class_type_name, "mailbox");
}

TEST(MailboxParameterizedElaborator, ParameterizedWithMethodCalls) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  int msg;\n"
      "  initial begin\n"
      "    mb.put(42);\n"
      "    mb.get(msg);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(MailboxParameterizedElaborator, MismatchedPutVariableRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  initial begin\n"
      "    mb.put(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to mailbox method 'put' is not type-equivalent", 5, "15.4.9"));
}

TEST(MailboxParameterizedElaborator, MismatchedPutLiteralRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  initial begin\n"
      "    mb.put(\"hello\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to mailbox method 'put' is not type-equivalent", 4, "15.4.9"));
}

TEST(MailboxParameterizedElaborator, MismatchedGetDestinationRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(string) mb;\n"
      "  int n;\n"
      "  initial begin\n"
      "    mb.get(n);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to mailbox method 'get' is not type-equivalent", 5, "15.4.9"));
}

TEST(MailboxParameterizedElaborator, TypedefMatchingArgsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef mailbox #(string) s_mbox;\n"
      "  s_mbox sm;\n"
      "  string s;\n"
      "  initial begin\n"
      "    sm.put(\"hello\");\n"
      "    sm.get(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(MailboxParameterizedElaborator, DynamicMailboxNotTypeChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  string s;\n"
      "  initial begin\n"
      "    mb.put(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(MailboxParameterizedElaborator, MismatchedTryPutRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  int got;\n"
      "  initial begin\n"
      "    got = mb.try_put(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to mailbox method 'try_put' is not type-equivalent", 6,
      "15.4.9"));
}

TEST(MailboxParameterizedElaborator, MismatchedPeekRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  initial begin\n"
      "    mb.peek(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to mailbox method 'peek' is not type-equivalent", 5, "15.4.9"));
}

TEST(MailboxParameterizedElaborator, MismatchedTryPeekRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  int got;\n"
      "  initial begin\n"
      "    got = mb.try_peek(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to mailbox method 'try_peek' is not type-equivalent", 6,
      "15.4.9"));
}

TEST(MailboxParameterizedElaborator, MismatchedTryGetRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  int got;\n"
      "  initial begin\n"
      "    got = mb.try_get(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to mailbox method 'try_get' is not type-equivalent", 6,
      "15.4.9"));
}

TEST(MailboxParameterizedElaborator, RealElementRejectsStringArgument) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(real) mb;\n"
      "  string s;\n"
      "  initial begin\n"
      "    mb.put(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to mailbox method 'put' is not type-equivalent", 5, "15.4.9"));
}

TEST(MailboxParameterizedElaborator, RealLiteralIntoIntMailboxRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  initial begin\n"
      "    mb.put(1.5);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to mailbox method 'put' is not type-equivalent", 4, "15.4.9"));
}

TEST(MailboxParameterizedElaborator, RealElementAcceptsRealArgument) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(real) mb;\n"
      "  real r;\n"
      "  initial begin\n"
      "    mb.put(r);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(MailboxParameterizedElaborator, MismatchedPutInTaskBodyRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  task do_send;\n"
      "    mb.put(s);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to mailbox method 'put' is not type-equivalent", 5, "15.4.9"));
}

TEST(MailboxParameterizedElaborator,
     MismatchedPutInAssertionPassStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  initial assert (1) mb.put(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to mailbox method 'put' is not type-equivalent", 4, "15.4.9"));
}

TEST(MailboxParameterizedElaborator,
     MismatchedPutInAssertionFailStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  initial assert (1) else mb.put(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to mailbox method 'put' is not type-equivalent", 4, "15.4.9"));
}

TEST(MailboxParameterizedElaborator, MismatchedPutInRandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  initial randcase\n"
      "    1 : mb.put(s);\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to mailbox method 'put' is not type-equivalent", 5, "15.4.9"));
}

TEST(MailboxParameterizedElaborator,
     MismatchedPutInRandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { mb.put(s); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to mailbox method 'put' is not type-equivalent", 6, "15.4.9"));
}

TEST(MailboxParameterizedElaborator,
     MismatchedPutInRandsequenceWeightCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { mb.put(s); };\n"
      "      alt : { n = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to mailbox method 'put' is not type-equivalent", 7, "15.4.9"));
}

}  // namespace
