#include <gtest/gtest.h>

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

}  // namespace
