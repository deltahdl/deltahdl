#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ArrayOrderingElaboration, ArrayReverseOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:2];\n"
             "  initial arr.reverse();\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, ArraySortOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  initial arr.sort;\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, ArrayRsortOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  initial arr.rsort;\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, ArrayShuffleOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  initial arr.shuffle();\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, SortWithClauseOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  initial arr.sort with (item);\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, RsortWithClauseOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  initial arr.rsort with (item);\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, SortOnDynamicArrayOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int a [] = '{3, 1, 2};\n"
             "  initial a.sort();\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, SortOnQueueOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q [$] = '{3, 1, 2};\n"
             "  initial q.sort;\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, ReverseWithClauseIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [0:3];\n"
      "  initial arr.reverse() with (item);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'reverse' does not accept a "
                            "'with' clause",
                            3, "7.12.2"));
}

TEST(ArrayOrderingElaboration, ShuffleWithClauseIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [0:3];\n"
      "  initial arr.shuffle() with (item);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'shuffle' does not accept a "
                            "'with' clause",
                            3, "7.12.2"));
}

TEST(ArrayOrderingElaboration, SortOnAssocArrayIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial arr.sort();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'sort' cannot be applied to "
                            "associative array 'arr'",
                            3, "7.12.2"));
}

TEST(ArrayOrderingElaboration, RsortOnAssocArrayIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial arr.rsort();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'rsort' cannot be applied "
                            "to associative array 'arr'",
                            3, "7.12.2"));
}

TEST(ArrayOrderingElaboration, ReverseOnAssocArrayIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial arr.reverse();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'reverse' cannot be applied "
                            "to associative array 'arr'",
                            3, "7.12.2"));
}

TEST(ArrayOrderingElaboration, ShuffleOnAssocArrayIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [int];\n"
      "  initial arr.shuffle();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'shuffle' cannot be applied "
                            "to associative array 'arr'",
                            3, "7.12.2"));
}

TEST(ArrayOrderingElaboration, SortOnAssocArrayInForkArmIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial begin\n"
      "    fork\n"
      "      arr.sort();\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'sort' cannot be applied to "
                            "associative array 'arr'",
                            5, "7.12.2"));
}

TEST(ArrayOrderingElaboration, SortOnAssocArrayInForStepIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 0; arr.sort()) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'sort' cannot be applied to "
                            "associative array 'arr'",
                            4, "7.12.2"));
}

TEST(ArrayOrderingElaboration, SortOnAssocArrayInAssertPassIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial assert (1) arr.sort();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'sort' cannot be applied to "
                            "associative array 'arr'",
                            3, "7.12.2"));
}

TEST(ArrayOrderingElaboration, SortOnAssocArrayInAssertFailIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial assert (1) else arr.sort();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'sort' cannot be applied to "
                            "associative array 'arr'",
                            3, "7.12.2"));
}

TEST(ArrayOrderingElaboration, SortOnAssocArrayInRandcaseItemIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial begin\n"
      "    randcase\n"
      "      1: arr.sort();\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'sort' cannot be applied to "
                            "associative array 'arr'",
                            5, "7.12.2"));
}

TEST(ArrayOrderingElaboration, SortOnAssocArrayInRandsequenceCodeBlockIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { arr.sort(); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'sort' cannot be applied to "
                            "associative array 'arr'",
                            5, "7.12.2"));
}

void ExpectOrderingReports(
    const ElabFixture& f, const std::string& prefix, const std::string& suffix,
    std::initializer_list<std::pair<const char*, uint32_t>> reports) {
  const auto& diags = f.diag.Diagnostics();
  for (auto [name, line] : reports) {
    std::string message = prefix;
    message += name;
    message += suffix;
    EXPECT_TRUE(ReportedError(diags, message, line, "7.12.2"))
        << name << " on line " << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), reports.size());
}

TEST(ArrayOrderingElaboration,
     DISABLED_AssociativeArrayOrderingReportedInSubroutinesClassesAndPackages) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  int q[$];\n"
      "  function automatic void f();\n"
      "    aa.sort;\n"
      "    q.sort;\n"
      "  endfunction\n"
      "  class C;\n"
      "    int ca[string];\n"
      "    int cq[$];\n"
      "    task t();\n"
      "      ca.rsort;\n"
      "      cq.rsort;\n"
      "    endtask\n"
      "  endclass\n"
      "endmodule\n"
      "package p;\n"
      "  int pa[byte];\n"
      "  int pd[];\n"
      "  function automatic void g();\n"
      "    pa.shuffle;\n"
      "    pd.shuffle;\n"
      "    pa.reverse;\n"
      "  endfunction\n"
      "endpackage\n",
      f);
  ExpectOrderingReports(
      f, "array ordering method '", "' cannot be applied to associative array",
      {{"sort", 5}, {"rsort", 12}, {"shuffle", 21}, {"reverse", 23}});
}

TEST(ArrayOrderingElaboration,
     DISABLED_WithClauseOnReverseOrShuffleReportedInSubroutinesAndClasses) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  function automatic void f();\n"
      "    q.reverse with (item);\n"
      "    q.sort with (item);\n"
      "  endfunction\n"
      "  class C;\n"
      "    int cq[4];\n"
      "    task t();\n"
      "      cq.shuffle() with (item);\n"
      "      cq.rsort with (item);\n"
      "    endtask\n"
      "  endclass\n"
      "endmodule\n"
      "package p;\n"
      "  function automatic void g();\n"
      "    int d[];\n"
      "    d.reverse() with (item + 1);\n"
      "    d.reverse;\n"
      "  endfunction\n"
      "endpackage\n",
      f);
  ExpectOrderingReports(f, "array ordering method '",
                        "' does not accept a 'with' clause",
                        {{"reverse", 4}, {"shuffle", 10}, {"reverse", 18}});
}

TEST(ArrayOrderingElaboration,
     DISABLED_SortOverTypesWithoutRelationalOperatorsReportedEverywhere) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; } s_t;\n"
      "  int m2[2][3];\n"
      "  s_t sa[3];\n"
      "  initial begin\n"
      "    m2.sort;\n"
      "    m2.rsort;\n"
      "    m2.reverse;\n"
      "    m2.shuffle;\n"
      "    m2.sort with (item[0]);\n"
      "  end\n"
      "  function automatic void f();\n"
      "    sa.sort;\n"
      "    sa.sort with (item.a);\n"
      "  endfunction\n"
      "  class C;\n"
      "    s_t ca[2];\n"
      "    task t();\n"
      "      ca.rsort with (item);\n"
      "      ca.rsort with (item.a);\n"
      "    endtask\n"
      "  endclass\n"
      "endmodule\n"
      "package p;\n"
      "  typedef struct { int a; } ps_t;\n"
      "  function automatic void g();\n"
      "    ps_t pa[2];\n"
      "    pa.sort;\n"
      "    pa.reverse;\n"
      "  endfunction\n"
      "endpackage\n",
      f);
  ExpectOrderingReports(
      f, "array method '",
      "' compares values of a type without relational operators",
      {{"sort", 6}, {"rsort", 7}, {"sort", 13}, {"rsort", 19}, {"sort", 28}});
}

TEST(ArrayOrderingElaboration, DISABLED_OrderingMethodUsedAsAValueIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = q.sort();\n"
      "    x = q.rsort with (item) + 1;\n"
      "    $display(\"%0d\", q.reverse);\n"
      "    if (q.shuffle()) x = 0;\n"
      "    q.sort();\n"
      "    q.rsort with (item);\n"
      "    q.reverse;\n"
      "    q.shuffle();\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectOrderingReports(
      f, "void function '", "' used as expression operand",
      {{"sort", 5}, {"rsort", 6}, {"reverse", 7}, {"shuffle", 8}});
}

}  // namespace
