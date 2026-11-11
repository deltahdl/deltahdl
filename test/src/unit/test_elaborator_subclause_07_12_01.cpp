#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <iterator>
#include <string>
#include <utility>

#include "elaborator/elaborator.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ArrayLocatorWildcard, FindIndexOnWildcardIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  int idx[$];\n"
      "  initial idx = aa.find_index with (item > 0);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'find_index' is not allowed on wildcard "
                            "associative array 'aa'",
                            4, "7.8.1"));
}

TEST(ArrayLocatorWildcard, UniqueIndexOnWildcardIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  int idx[$];\n"
      "  initial idx = aa.unique_index with (item > 0);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'unique_index' is not allowed on wildcard "
                            "associative array 'aa'",
                            4, "7.8.1"));
}

TEST(ArrayLocatorWildcard, ElementFindOnWildcardIsAllowed) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  int found[$];\n"
      "  initial found = aa.find with (item > 0);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArrayLocatorValidation, ComparingValuesWithoutRelationalOperators) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class C; int v; endclass\n"
      "  typedef struct { int a; } s_t;\n"
      "  typedef enum {A, B} e_t;\n"
      "  C ca[3];\n"
      "  s_t sa[3];\n"
      "  C cq[$];\n"
      "  s_t sq[$];\n"
      "  e_t ea[2];\n"
      "  e_t ea2[2];\n"
      "  int k;\n"
      "  initial begin\n"
      "    ca.sort;\n"
      "    sq = sa.min;\n"
      "    cq = ca.unique;\n"
      "    sa.rsort with (item);\n"
      "    sa.sort with (item.a);\n"
      "    sa.sort(x) with (x);\n"
      "    ca.sort with (k);\n"
      "    sq = sa.max(y) with (y.a);\n"
      "    ea.sort;\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags,
                            "array method 'sort' compares values of a type "
                            "without relational operators",
                            13, "7.12.2"));
  EXPECT_TRUE(ReportedError(diags,
                            "array method 'min' compares values of a type "
                            "without relational operators",
                            14, "7.12.1"));
  EXPECT_TRUE(ReportedError(diags,
                            "array method 'unique' compares values of a type "
                            "without relational operators",
                            15, "7.12.1"));
  EXPECT_TRUE(ReportedError(diags,
                            "array method 'rsort' compares values of a type "
                            "without relational operators",
                            16, "7.12.2"));
  EXPECT_TRUE(ReportedError(diags,
                            "array method 'sort' compares values of a type "
                            "without relational operators",
                            18, "7.12.2"));
  for (const auto& d : diags) {
    EXPECT_NE(d.loc.line, 17u) << d.message;
    EXPECT_FALSE(d.loc.line >= 19 && d.loc.line <= 21)
        << d.loc.line << ": " << d.message;
  }
}

TEST(BuiltinMethodElaboration,
     WithExpressionOfAnyFormNeedsRelationalOperators) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class C; int v; endclass\n"
      "  typedef struct { C h; int a; int arr[2]; } s_t;\n"
      "  typedef struct { s_t inner; } o_t;\n"
      "  s_t sa[3];\n"
      "  s_t sq[$];\n"
      "  o_t oa[2];\n"
      "  o_t oq[$];\n"
      "  C ca[3];\n"
      "  C cq[$];\n"
      "  C hv;\n"
      "  initial begin\n"
      "    sq = sa.min with (item.h);\n"
      "    sa.sort with (item.arr);\n"
      "    oq = oa.min with (item.inner.h);\n"
      "    sq = sa.max with (item.a);\n"
      "    oq = oa.min with (item.inner.a);\n"
      "    cq = ca.min with (item.v);\n"
      "    sq = sa.unique with (item.zz);\n"
      "    cq = ca.max with (hv.v);\n"
      "    sq = sa.min with (item.arr[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const char* const kReport =
      "compares values of a type without relational operators";
  EXPECT_TRUE(ReportedError(diags, kReport, 13, "7.12.1"));
  EXPECT_TRUE(ReportedError(diags, kReport, 14, "7.12.2"));
  EXPECT_TRUE(ReportedError(diags, kReport, 15, "7.12.1"));
  for (const auto& d : diags) {
    EXPECT_FALSE(d.loc.line >= 16 && d.loc.line <= 21 &&
                 d.message.find(kReport) != std::string::npos)
        << d.loc.line << ": " << d.message;
  }
}

void ExpectMissingWithReports(
    const ElabFixture& f,
    std::initializer_list<std::pair<const char*, uint32_t>> missing) {
  const auto& diags = f.diag.Diagnostics();
  for (const auto& [method, line] : missing) {
    EXPECT_TRUE(ReportedError(diags,
                              std::string("array locator method '") + method +
                                  "' requires a 'with' clause",
                              line, "7.12.1"))
        << method << " on line " << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), missing.size());
}

TEST(ArrayLocatorValidation,
     MissingWithClauseReportedInAModuleProcedureBesideAllowedOmissions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a[3], q[$];\n"
      "  initial begin\n"
      "    q = a.find;\n"
      "    q = a.find_index;\n"
      "    q = a.find_first;\n"
      "    q = a.find_first_index;\n"
      "    q = a.find_last;\n"
      "    q = a.find_last_index;\n"
      "    q = a.min;\n"
      "    q = a.max;\n"
      "    q = a.unique;\n"
      "    q = a.unique_index;\n"
      "    q = a.find_last_index with (item == 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectMissingWithReports(f, {{"find", 4},
                               {"find_index", 5},
                               {"find_first", 6},
                               {"find_first_index", 7},
                               {"find_last", 8},
                               {"find_last_index", 9}});
}

TEST(ArrayLocatorValidation,
     DISABLED_MissingWithClauseReportedInSubroutinesClassesAndPackages) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a[3], q[$];\n"
      "  function automatic void f();\n"
      "    q = a.find;\n"
      "    q = a.find with (item > 0);\n"
      "  endfunction\n"
      "  class C;\n"
      "    int b[3], r[$];\n"
      "    task t();\n"
      "      r = b.find_last_index;\n"
      "      r = b.unique;\n"
      "      r = b.min;\n"
      "    endtask\n"
      "  endclass\n"
      "endmodule\n"
      "package p;\n"
      "  function automatic int g();\n"
      "    int a[3], q[$];\n"
      "    q = a.find_first;\n"
      "    q = a.max;\n"
      "    return q.size();\n"
      "  endfunction\n"
      "endpackage\n",
      f);
  ExpectMissingWithReports(
      f, {{"find", 4}, {"find_last_index", 10}, {"find_first", 19}});
}

TEST(ArrayLocatorWildcard,
     DISABLED_IndexLocatorOnAWildcardArrayReportedInSubroutinesAndClasses) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[*];\n"
      "  int q[$];\n"
      "  function automatic void f();\n"
      "    q = aa.find_index with (item > 0);\n"
      "    q = aa.find with (item > 0);\n"
      "  endfunction\n"
      "  class C;\n"
      "    int wa[*];\n"
      "    int r[$];\n"
      "    function void g();\n"
      "      r = wa.find_first_index with (item > 0);\n"
      "      r = wa.find_last with (item > 0);\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n"
      "package p;\n"
      "  int pa[*];\n"
      "  function automatic int h();\n"
      "    int s[$];\n"
      "    s = pa.unique_index;\n"
      "    s = pa.unique;\n"
      "    return s.size();\n"
      "  endfunction\n"
      "endpackage\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'find_index' is not allowed on wildcard associative array 'aa'",
      5, "7.8.1"));
  EXPECT_TRUE(ReportedError(
      diags,
      "'find_first_index' is not allowed on wildcard associative array 'wa'",
      12, "7.8.1"));
  EXPECT_TRUE(ReportedError(
      diags, "'unique_index' is not allowed on wildcard associative array 'pa'",
      21, "7.8.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(ArrayLocatorValidation,
     DISABLED_TypesWithoutRelationalOperatorsReportedInSubroutinesAndClasses) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; } s_t;\n"
      "  s_t sa[3], sq[$];\n"
      "  function automatic void f();\n"
      "    sq = sa.min;\n"
      "    sq = sa.min with (item.a);\n"
      "  endfunction\n"
      "  class C;\n"
      "    s_t ca[2], cq[$];\n"
      "    int iq[$];\n"
      "    task t();\n"
      "      cq = ca.unique;\n"
      "      iq = ca.unique_index;\n"
      "      cq = ca.max with (item);\n"
      "      cq = ca.unique with (item.a);\n"
      "    endtask\n"
      "  endclass\n"
      "endmodule\n"
      "package p;\n"
      "  typedef struct { int a; } ps_t;\n"
      "  function automatic int g();\n"
      "    ps_t pa[2], pq[$];\n"
      "    pq = pa.max;\n"
      "    return pq.size();\n"
      "  endfunction\n"
      "endpackage\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const std::pair<const char*, uint32_t> kNoRelational[] = {
      {"min", 5},
      {"unique", 12},
      {"unique_index", 13},
      {"max", 14},
      {"max", 23}};
  for (const auto& [method, line] : kNoRelational) {
    EXPECT_TRUE(ReportedError(diags,
                              std::string("array method '") + method +
                                  "' compares values of a type without "
                                  "relational operators",
                              line, "7.12.1"))
        << method << " on line " << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), std::size(kNoRelational));
}

TEST(ArrayLocatorValidation, DISABLED_NonBooleanWithExpressionIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int x; } s_t;\n"
      "  s_t sv;\n"
      "  int u[2];\n"
      "  int a[3], q[$];\n"
      "  real r;\n"
      "  function automatic void f();\n"
      "    q = a.find with (sv);\n"
      "    q = a.find with (item * 2);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    q = a.find_index with (u);\n"
      "    q = a.find_first with (sv);\n"
      "    q = a.find_last_index with (r * item);\n"
      "    q = a.find_last with (item > 1 && item < 5);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line : {8u, 12u, 13u}) {
    EXPECT_TRUE(ReportedError(diags, "does not evaluate to a Boolean value",
                              line, "7.12.1"))
        << "line " << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

}  // namespace
