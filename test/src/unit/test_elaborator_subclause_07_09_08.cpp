#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssocTraversalArgElaboration, IntegralArgOnIntegralIndexOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int aa[int];\n"
             "  int k;\n"
             "  initial k = aa.first(k);\n"
             "endmodule\n"));
}

TEST(AssocTraversalArgElaboration, NarrowIntegralArgOnIntegralIndexOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int aa[int];\n"
             "  byte ix;\n"
             "  int status;\n"
             "  initial status = aa.first(ix);\n"
             "endmodule\n"));
}

TEST(AssocTraversalArgElaboration, StringArgOnStringIndexOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int aa[string];\n"
             "  string s;\n"
             "  initial s = aa.last(s);\n"
             "endmodule\n"));
}

TEST(AssocTraversalArgElaboration, StringArgOnIntegralIndexRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  string s;\n"
      "  int status;\n"
      "  initial status = aa.first(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "traversal method 'first' argument is not "
                            "assignment compatible with the index type of "
                            "associative array 'aa'",
                            5, "7.9.8"));
}

TEST(AssocTraversalArgElaboration, IntegralArgOnStringIndexRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int k;\n"
      "  initial k = aa.last(k);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "traversal method 'last' argument is not "
                            "assignment compatible with the index type of "
                            "associative array 'aa'",
                            4, "7.9.8"));
}

TEST(AssocTraversalArgElaboration, NextStringArgOnIntegralIndexRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  string s;\n"
      "  int status;\n"
      "  initial status = aa.next(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "traversal method 'next' argument is not "
                            "assignment compatible with the index type of "
                            "associative array 'aa'",
                            5, "7.9.8"));
}

TEST(AssocTraversalArgElaboration, PrevIntegralArgOnStringIndexRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int k;\n"
      "  initial k = aa.prev(k);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "traversal method 'prev' argument is not "
                            "assignment compatible with the index type of "
                            "associative array 'aa'",
                            4, "7.9.8"));
}

TEST(AssocTraversalArgElaboration,
     ConditionPositionStringArgOnIntegralIndexRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  string s;\n"
      "  int status;\n"
      "  initial if (aa.first(s)) status = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "traversal method 'first' argument is not "
                            "assignment compatible with the index type of "
                            "associative array 'aa'",
                            5, "7.9.8"));
}

TEST(AssocTraversalArgElaboration, StringArgOnIntegralIndexInForkArmRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  string s;\n"
      "  int status;\n"
      "  initial begin\n"
      "    fork\n"
      "      status = aa.first(s);\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "traversal method 'first' argument is not "
                            "assignment compatible with the index type of "
                            "associative array 'aa'",
                            7, "7.9.8"));
}

TEST(AssocTraversalArgElaboration, StringArgOnIntegralIndexInForInitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  string s;\n"
      "  int status;\n"
      "  integer i;\n"
      "  initial for (status = aa.first(s); i < 0; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "traversal method 'first' argument is not "
                            "assignment compatible with the index type of "
                            "associative array 'aa'",
                            6, "7.9.8"));
}

TEST(AssocTraversalArgElaboration, StringArgOnIntegralIndexInForStepRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  string s;\n"
      "  int status;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 0; status = aa.first(s)) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "traversal method 'first' argument is not "
                            "assignment compatible with the index type of "
                            "associative array 'aa'",
                            6, "7.9.8"));
}

TEST(AssocTraversalArgElaboration,
     StringArgOnIntegralIndexInAssertPassRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  string s;\n"
      "  int status;\n"
      "  initial assert (1) status = aa.first(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "traversal method 'first' argument is not "
                            "assignment compatible with the index type of "
                            "associative array 'aa'",
                            5, "7.9.8"));
}

TEST(AssocTraversalArgElaboration,
     StringArgOnIntegralIndexInAssertFailRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  string s;\n"
      "  int status;\n"
      "  initial assert (1) else status = aa.first(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "traversal method 'first' argument is not "
                            "assignment compatible with the index type of "
                            "associative array 'aa'",
                            5, "7.9.8"));
}

TEST(AssocTraversalArgElaboration,
     StringArgOnIntegralIndexInRandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  string s;\n"
      "  int status;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1: status = aa.first(s);\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "traversal method 'first' argument is not "
                            "assignment compatible with the index type of "
                            "associative array 'aa'",
                            7, "7.9.8"));
}

TEST(AssocTraversalArgElaboration,
     StringArgOnIntegralIndexInRandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  string s;\n"
      "  int status;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { status = aa.first(s); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "traversal method 'first' argument is not "
                            "assignment compatible with the index type of "
                            "associative array 'aa'",
                            7, "7.9.8"));
}

}  // namespace
