#include <gtest/gtest.h>

#include <cstdint>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssocArrayElaboration, MarkedAssociative) {
  ElabFixture f;
  auto* design = Elaborate("module m; int aa[int]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_assoc);
}

TEST(AssocArrayElaboration, ElementWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [7:0] aa[int]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "aa") {
      EXPECT_EQ(v.width, 8u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(AssocArrayElaboration, MultipleArrays) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int a[int];\n"
             "  string b[string];\n"
             "endmodule\n"));
}

TEST(AssocArrayElaboration, WholeAssocInArithExprRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  initial x = aa + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array operand requires an element "
                            "selection before use in this expression",
                            4, "7.4.6"));
}

TEST(AssocArrayElaboration, WholeAssocEqualityComparisonAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int aa[int];\n"
             "  int bb[int];\n"
             "  logic eq;\n"
             "  initial eq = (aa == bb);\n"
             "endmodule\n"));
}

TEST(AssocArrayElaboration, WholeAssocCopyAssignmentAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int aa[int];\n"
             "  int bb[int];\n"
             "  initial bb = aa;\n"
             "endmodule\n"));
}

TEST(AssocArrayElaboration, AssocSliceRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  initial x = aa[1:2];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice is not allowed on an associative array", 4,
                            "7.4.6"));
}

TEST(AssocArrayElaboration, AssocSliceInForkArmRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  initial begin\n"
      "    fork\n"
      "      x = aa[1:2];\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice is not allowed on an associative array", 6,
                            "7.4.6"));
}

TEST(AssocArrayElaboration, AssocSliceInForInitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  integer i;\n"
      "  initial for (x = aa[1:2]; i < 0; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice is not allowed on an associative array", 5,
                            "7.4.6"));
}

TEST(AssocArrayElaboration, AssocSliceInForStepRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 0; x = aa[1:2]) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice is not allowed on an associative array", 5,
                            "7.4.6"));
}

TEST(AssocArrayElaboration, AssocSliceInAssertPassRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  initial assert (1) x = aa[1:2];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice is not allowed on an associative array", 4,
                            "7.4.6"));
}

TEST(AssocArrayElaboration, AssocSliceInAssertFailRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  initial assert (1) else x = aa[1:2];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice is not allowed on an associative array", 4,
                            "7.4.6"));
}

TEST(AssocArrayElaboration, AssocSliceInRandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1: x = aa[1:2];\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice is not allowed on an associative array", 6,
                            "7.4.6"));
}

TEST(AssocArrayElaboration, AssocSliceInRandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = aa[1:2]; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice is not allowed on an associative array", 6,
                            "7.4.6"));
}

TEST(AssocArrayElaboration, IndexKeywordIsRecorded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m; typedef int idx_t;\n"
      "  int a [int]; int b [integer]; int c [bit]; int d [logic];\n"
      "  int e [idx_t];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const auto& vars = design->top_modules[0]->variables;
  ASSERT_EQ(vars.size(), 5U);
  EXPECT_EQ(vars[0].assoc_index_keyword, "int");
  EXPECT_EQ(vars[1].assoc_index_keyword, "integer");
  EXPECT_EQ(vars[2].assoc_index_keyword, "bit");
  EXPECT_EQ(vars[3].assoc_index_keyword, "logic");
  EXPECT_EQ(vars[4].assoc_index_keyword, "");
  EXPECT_EQ(vars[4].assoc_index_type_name, "idx_t");
}

TEST(AssociativeArrayElaboration, DISABLED_IndexTypeDeclaringATypeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int e1 [enum {A, B}];\n"
      "  int e2 [enum bit [1:0] {C, D}];\n"
      "  int s1 [struct packed {bit [3:0] f;}];\n"
      "  int s2 [struct {int f;}];\n"
      "  int u1 [union packed {bit [3:0] a; bit [3:0] b;}];\n"
      "  int u2 [union {int a; byte b;}];\n"
      "  int x [int][enum {E, F}];\n"
      "  int q [struct {real f;}];\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line = 2; line <= 9; ++line) {
    EXPECT_TRUE(ReportedError(
        diags, "index type of an associative array shall not declare a type",
        line, "7.8"))
        << line;
  }
  EXPECT_TRUE(ReportedError(diags, "real or shortreal type shall not be used",
                            9, "7.8.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 9u);
}

TEST(AssociativeArrayElaboration,
     DISABLED_IndexTypeDeclaringATypeIsReportedInEveryScope) {
  ElabFixture f;
  ElaborateSrc(
      "package p; int a [enum {A1, B1}]; endpackage\n"
      "int g [enum {A2, B2}];\n"
      "class K; int c [enum {A3, B3}]; endclass\n"
      "interface I; int i [enum {A4, B4}]; endinterface\n"
      "program P; int r [enum {A5, B5}]; endprogram\n"
      "module t;\n"
      "  function void f(int a [enum {A6, B6}]);\n"
      "    int l [enum {A7, B7}]; endfunction\n"
      "  initial begin int b [enum {A8, B8}]; end\n"
      "  I ii(); P pp();\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line : {1u, 2u, 3u, 4u, 5u, 7u, 8u, 9u}) {
    EXPECT_TRUE(ReportedError(
        diags, "index type of an associative array shall not declare a type",
        line, "7.8"))
        << line;
  }
}

TEST(AssociativeArrayElaboration, IndexTypeNamingATypeIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class Q #(int W = 1); endclass\n"
      "module t;\n"
      "  typedef enum {A, B} e_t; int e [e_t];\n"
      "  typedef struct packed {bit [3:0] f;} s_t; int s [s_t];\n"
      "  typedef union packed {bit [3:0] a; bit [3:0] b;} u_t; int u [u_t];\n"
      "  int k; int t1 [type(k)]; int c [Q#(8)];\n"
      "  int b [byte]; int i [int unsigned]; int x [int][e_t];\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
