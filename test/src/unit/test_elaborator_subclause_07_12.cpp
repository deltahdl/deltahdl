#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ArrayMethodValidation, NameNoMethodOfTheArraysKindIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int fx[3];\n"
      "  int dy[];\n"
      "  int aa[string];\n"
      "  int q[$];\n"
      "  int n;\n"
      "  initial begin\n"
      "    q.foo();\n"
      "    dy.push_back(1);\n"
      "    aa.pop_front();\n"
      "    n = fx.size();\n"
      "    q.h.run();\n"
      "    q.push_back(1);\n"
      "    dy.delete();\n"
      "    n = aa.exists(\"a\");\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'foo' is not a built-in method of the queue 'q'", 8, "7.10.2"));
  EXPECT_TRUE(ReportedError(
      diags, "'push_back' is not a built-in method of the dynamic array 'dy'",
      9, "7.5"));
  EXPECT_TRUE(ReportedError(
      diags,
      "'pop_front' is not a built-in method of the associative array 'aa'", 10,
      "7.9"));
  EXPECT_TRUE(ReportedError(
      diags, "'size' is not a built-in method of the fixed-size array 'fx'", 11,
      "7.12"));
  EXPECT_TRUE(ReportedError(
      diags, "'h' is not a built-in method of the queue 'q'", 12, "7.10.2"));
  for (const auto& d : diags) {
    EXPECT_FALSE(d.loc.line >= 13 && d.loc.line <= 15)
        << d.loc.line << ": " << d.message;
  }
}

TEST(ArrayMethodValidation, AMemberArraysNameOfNoMethodIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct { int q[$]; int fx[2]; rand int ra[2]; } s_t;\n"
      "  class C; int q[$]; int aa[string]; rand int ra[2]; endclass\n"
      "  s_t s; C h = new; int n;\n"
      "  initial begin\n"
      "    s.q.foo();\n"
      "    h.q.bar();\n"
      "    s.fx.delete();\n"
      "    h.aa.pop_front();\n"
      "    h.ra.baz();\n"
      "    s.ra.rand_mode(0);\n"
      "    s.q.delete();\n"
      "    n = h.q.size();\n"
      "    n = h.aa.num();\n"
      "    s.fx.sort();\n"
      "    h.ra.rand_mode(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'foo' is not a built-in method of the queue 's.q'", 6, "7.10.2"));
  EXPECT_TRUE(ReportedError(
      diags, "'bar' is not a built-in method of the queue 'h.q'", 7, "7.10.2"));
  EXPECT_TRUE(ReportedError(
      diags, "'delete' is not a built-in method of the fixed-size array 's.fx'",
      8, "7.12"));
  EXPECT_TRUE(ReportedError(
      diags,
      "'pop_front' is not a built-in method of the associative array 'h.aa'", 9,
      "7.9"));
  EXPECT_TRUE(ReportedError(
      diags, "'baz' is not a built-in method of the fixed-size array 'h.ra'",
      10, "7.12"));
  EXPECT_TRUE(ReportedError(
      diags,
      "'rand_mode' is not a built-in method of the fixed-size array 's.ra'", 11,
      "7.12"));
  for (const auto& d : diags) {
    EXPECT_FALSE(d.loc.line >= 12 && d.loc.line <= 16)
        << d.loc.line << ": " << d.message;
  }
}

TEST(ArrayMethodValidation, AMembersNamedIndexTypeMakesItAssociative) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef int idx_t;\n"
      "  class K; endclass\n"
      "  class C; int bt[idx_t]; int bk[K]; endclass\n"
      "  C h = new; int n;\n"
      "  initial begin\n"
      "    n = h.bt.num();\n"
      "    n = h.bk.num();\n"
      "  end\n"
      "endmodule\n",
      f);
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_FALSE(d.loc.line >= 7 && d.loc.line <= 8)
        << d.loc.line << ": " << d.message;
  }
}

TEST(ArrayMethodValidation, AClassTypeParameterDimensionMakesItAssociative) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class Box #(type T = int, int N = 3); int m[T]; int f[N]; endclass\n"
      "  class Sub extends Box #(string); endclass\n"
      "  Box #(string, 6) b = new; Sub s = new; int n;\n"
      "  initial begin\n"
      "    n = b.m.num();\n"
      "    n = s.m.num();\n"
      "    n = b.f.num();\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'num' is not a built-in method of the fixed-size array 'b.f'", 8,
      "7.12"));
  for (const auto& d : diags) {
    EXPECT_FALSE(d.loc.line >= 6 && d.loc.line <= 7)
        << d.loc.line << ": " << d.message;
  }
}

TEST(ArrayMethodValidation, AClassTypedefDimensionMakesItAssociative) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class C; typedef int J; typedef int K; int m[K]; int f[4]; endclass\n"
      "  class D extends C; int d[K]; endclass\n"
      "  C c = new; D h = new; int n;\n"
      "  initial begin\n"
      "    n = c.m.num();\n"
      "    n = h.m.num();\n"
      "    n = h.d.num();\n"
      "    n = c.f.num();\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'num' is not a built-in method of the fixed-size array 'c.f'", 9,
      "7.12"));
  for (const auto& d : diags) {
    EXPECT_FALSE(d.loc.line >= 6 && d.loc.line <= 8)
        << d.loc.line << ": " << d.message;
  }
}

TEST(ArrayMethodValidation, ReceiversNotOneMemberOfAVariablePassClean) {
  ElabFixture f;
  ElaborateSrc(
      "package p; int q[$]; endpackage\n"
      "module child; int q[$]; endmodule\n"
      "module top;\n"
      "  typedef struct { int q[$]; } in_t;\n"
      "  typedef struct { in_t in; string str; } out_t;\n"
      "  out_t ss; int ar[2][$]; int n;\n"
      "  child u();\n"
      "  initial begin\n"
      "    ss.in.q.delete();\n"
      "    p::q.delete();\n"
      "    ar[0].delete();\n"
      "    u.q.delete();\n"
      "    n = ss.str.len();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_FALSE(d.loc.line >= 9 && d.loc.line <= 13)
        << d.loc.line << ": " << d.message;
  }
}

TEST(ArrayMethodValidation, MissingWithClauseReportedAtElaboration) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int q[$] = '{1, 2, 3};\n"
      "  int r[$];\n"
      "  bit go = 0;\n"
      "  initial if (go) begin\n"
      "    r = q.find(x);\n"
      "    r = q.find_index;\n"
      "    r = q.map();\n"
      "    q.sort(x);\n"
      "    r = q.find with (item > 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, "iterator argument without 'with' clause", 6,
                            "7.12"));
  EXPECT_TRUE(ReportedError(
      diags, "array locator method 'find_index' requires a 'with' clause", 7,
      "7.12.1"));
  EXPECT_TRUE(ReportedError(
      diags, "array method 'map' requires a 'with' clause", 8, "7.12.5"));
  EXPECT_TRUE(ReportedError(diags, "iterator argument without 'with' clause", 9,
                            "7.12"));
  for (const auto& d : diags) EXPECT_NE(d.loc.line, 10u) << d.message;
}

TEST(ArrayMethodElaboration,
     IteratorArgumentWithoutWithReportedForEveryMethodKind) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a [3]; int b []; int s;\n"
      "  initial begin\n"
      "    s = a.sum(x);\n"
      "    b = a.map(z);\n"
      "    a.sort(w);\n"
      "    s = a.sum(v) with (v + 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line : {4u, 5u, 6u}) {
    EXPECT_TRUE(ReportedError(diags, "iterator argument without 'with' clause",
                              line, "7.12"))
        << line;
  }
  EXPECT_FALSE(ReportedError(diags, "iterator argument without 'with' clause",
                             7, "7.12"));
}

TEST(ArrayMethodElaboration,
     DISABLED_IteratorArgumentWithoutWithReportedInSubroutinesAndMethods) {
  ElabFixture f;
  ElaborateSrc(
      "class K;\n"
      "  int a [3];\n"
      "  function int f(); return a.sum(x); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int a [3];\n"
      "  function int g(); return a.product(y); endfunction\n"
      "  task tk; a.sort(w); endtask\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line : {3u, 7u, 8u}) {
    EXPECT_TRUE(ReportedError(diags, "iterator argument without 'with' clause",
                              line, "7.12"))
        << line;
  }
}

}  // namespace
