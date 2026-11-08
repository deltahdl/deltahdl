#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(StringConcatAndReplication, StringConcatElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string a, b, c;\n"
      "  initial begin\n"
      "    a = \"hello\";\n"
      "    b = \" world\";\n"
      "    c = {a, b};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringConcatAndReplication, StringReplicationElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial s = {3{\"ab\"}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringConcatAndReplication, NonConstantMultiplierAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    int n;\n"
      "    string s;\n"
      "    n = 3;\n"
      "    s = {n{\"boo \"}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringConcatAndReplication, StringConcatWithLiteralElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial s = {\"hello\", \" \", \"world\"};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringConcatAndReplication, StringConcatAppendElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = \"hello\";\n"
      "    s = {s, \" world\"};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringConcatAndReplication, StringConcatOnLhsBlockingAssignRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  initial {a, b} = \"hello\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            3, "11.4.12.2"));
}

TEST(StringConcatAndReplication, StringConcatOnLhsNonblockingAssignRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  initial {a, b} <= \"hello\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            3, "11.4.12.2"));
}

TEST(StringConcatAndReplication, StringConcatOnLhsContAssignRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  assign {a, b} = \"hello\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            3, "11.4.12.2"));
}

TEST(StringConcatAndReplication, BitConcatOnLhsStillAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  initial {a, b} = 8'hC3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringConcatAndReplication, StringConcatOnLhsInAForkStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  initial fork\n"
      "    {a, b} = \"hello\";\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            4, "11.4.12.2"));
}

TEST(StringConcatAndReplication, StringConcatOnLhsInAForInitializerRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  int i;\n"
      "  initial\n"
      "    for ({a, b} = \"hello\"; i < 1; i = i + 1)\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            5, "11.4.12.2"));
}

TEST(StringConcatAndReplication, StringConcatOnLhsInAForStepRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; {a, b} = \"hello\")\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            5, "11.4.12.2"));
}

TEST(StringConcatAndReplication,
     StringConcatOnLhsInAnAssertionPassStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  logic ok;\n"
      "  initial assert (ok) {a, b} = \"hello\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            4, "11.4.12.2"));
}

TEST(StringConcatAndReplication,
     StringConcatOnLhsInAnAssertionFailStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  logic armed;\n"
      "  initial assert (armed) else {a, b} = \"hello\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            4, "11.4.12.2"));
}

TEST(StringConcatAndReplication, StringConcatOnLhsInARandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  initial randcase 1: {a, b} = \"hello\"; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            3, "11.4.12.2"));
}

TEST(StringConcatAndReplication,
     StringConcatOnLhsInARandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { {a, b} = \"hello\"; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            5, "11.4.12.2"));
}

TEST(StringConcatAndReplication, MethodOfStringConcatenationIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  string s, t;\n"
      "  int n;\n"
      "  initial n = {s, t}.run();\n"
      "  initial n = {3{s}}.run();\n"
      "  initial n = {\"ab\", s}.len();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'run' is not a built-in method of the string a "
                            "concatenation yields",
                            4, "6.16"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'run' is not a built-in method of the string a "
                            "concatenation yields",
                            5, "6.16"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(StringConcatAndReplication, ConcatenationOfUnknownOperandIsUnchecked) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  int n;\n"
             "  initial n = {$sformatf(\"%0d\", n)}.len();\n"
             "endmodule\n"));
}

}  // namespace
