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

// The rule that rejects this is not §7.8 but §7.4.6, which requires an array
// operand to be selected down to an element before an arithmetic operator can
// take it, so the report names §7.4.6.
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

// §7.8 — the "select an element first" rule names two exceptions: copying and
// comparing whole arrays. Comparison is covered above; this exercises the copy
// exception: assigning one whole associative array to another (no element
// selection) shall be legal.
TEST(AssocArrayElaboration, WholeAssocCopyAssignmentAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int aa[int];\n"
             "  int bb[int];\n"
             "  initial bb = aa;\n"
             "endmodule\n"));
}

// §7.8 gives an associative array no slice, and the report
// WalkStmtsForAssocSlice emits names §7.4.6, which states the rule. Neither
// clause conditions it on the statement the slice is written in, and the walk
// wrote out six of the thirteen statement links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states, so a slice written in
// any of the other seven was never looked at. The cases below write the same
// `x = aa[1:2];` at the top level and then in each of those seven links.
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

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...` and
// A.6.2 gives `variable_assignment ::= variable_lvalue = expression`, so a
// slice may stand in the expression of a for-loop initialization.
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

// A.6.8 gives `for_step_assignment ::= operator_assignment | ...`.
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

// A.6.10 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, which is Stmt::assert_pass_stmt here and
// Stmt::assert_fail_stmt below.
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

// §18.16 and A.6.7 give `randcase_item ::= expression : statement_or_null`.
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

// §18.17 and A.6.12 give `rs_code_block ::= { { data_declaration } {
// statement_or_null } }`.
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

}  // namespace
