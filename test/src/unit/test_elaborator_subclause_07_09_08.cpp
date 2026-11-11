#include <gtest/gtest.h>

#include <cstdint>

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

TEST(BuiltinMethodElaboration,
     DISABLED_ArgumentNotCompatibleWithAClassEnumOrStructIndexIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class Base; endclass\n"
      "class Der extends Base; endclass\n"
      "class U; endclass\n"
      "module t;\n"
      "  typedef enum {A, B} e_t; typedef enum {X, Y} f_t;\n"
      "  typedef struct {int a;} s_t; typedef struct {int a;} r_t;\n"
      "  int ac [Base]; int ae [e_t]; int ai [int]; int as [string]; "
      "int au [s_t];\n"
      "  U u; Der d; int i; string s; f_t f; e_t e; chandle ch; Base b; "
      "r_t r;\n"
      "  initial begin\n"
      "    void'(ac.first(u));\n"
      "    void'(ac.last(i));\n"
      "    void'(ac.next(s));\n"
      "    void'(ac.prev(d));\n"
      "    void'(ae.first(f));\n"
      "    void'(ae.last(s));\n"
      "    void'(ai.next(e));\n"
      "    void'(ai.prev(b));\n"
      "    void'(as.first(ch));\n"
      "    void'(au.last(i));\n"
      "    void'(au.next(r));\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line = 10; line <= 20; ++line) {
    EXPECT_TRUE(ReportedError(diags,
                              "argument is not assignment compatible with the "
                              "index type of associative array",
                              line, "7.9.8"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 11u);
}

TEST(BuiltinMethodElaboration,
     DISABLED_ArgumentCheckReachesPropertiesHandlesAndMembers) {
  ElabFixture f;
  ElaborateSrc(
      "class K;\n"
      "  int aa [int]; string s;\n"
      "  function void f(); void'(aa.first(s)); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  typedef struct {int m [int];} h_t;\n"
      "  K o; h_t hv; string s;\n"
      "  initial begin\n"
      "    o = new; void'(o.aa.first(s));\n"
      "    void'(hv.m.last(s));\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line : {3u, 9u, 10u}) {
    EXPECT_TRUE(ReportedError(diags,
                              "argument is not assignment compatible with the "
                              "index type of associative array",
                              line, "7.9.8"))
        << line;
  }
}

TEST(BuiltinMethodElaboration,
     CompatibleArgumentOnAClassEnumStructChandleOrEventIndexIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class Base; endclass\n"
      "class Der extends Base; endclass\n"
      "module t;\n"
      "  typedef enum {A, B} e_t; typedef struct packed {bit [3:0] h;} p_t;\n"
      "  typedef struct {int a;} s_t;\n"
      "  int ac [Base]; int ae [e_t]; int ap [p_t]; int au [s_t];\n"
      "  int ach [chandle]; int aev [event]; int ad [Der];\n"
      "  Base b; e_t e; int i; s_t sv; chandle ch; event ev;\n"
      "  initial begin\n"
      "    void'(ac.first(b)); void'(ae.first(e)); void'(ae.next(i));\n"
      "    void'(ap.first(i)); void'(au.first(sv)); void'(ach.first(ch));\n"
      "    void'(aev.first(ev)); void'(ad.first(b));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
