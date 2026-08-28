#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §7.9.8 — an integral argument matches an integral index type and is therefore
// assignment compatible; elaboration accepts it.
TEST(AssocTraversalArgElaboration, IntegralArgOnIntegralIndexOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int aa[int];\n"
             "  int k;\n"
             "  initial k = aa.first(k);\n"
             "endmodule\n"));
}

// §7.9.8 — a narrower integral argument is still assignment compatible with an
// integral index. The truncation it produces is a run-time effect, so
// elaboration must not reject it (the LRM's own example pairs an int index with
// a byte argument).
TEST(AssocTraversalArgElaboration, NarrowIntegralArgOnIntegralIndexOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int aa[int];\n"
             "  byte ix;\n"
             "  int status;\n"
             "  initial status = aa.first(ix);\n"
             "endmodule\n"));
}

// §7.9.8 — a string argument matches a string index type and is assignment
// compatible; elaboration accepts it.
TEST(AssocTraversalArgElaboration, StringArgOnStringIndexOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int aa[string];\n"
             "  string s;\n"
             "  initial s = aa.last(s);\n"
             "endmodule\n"));
}

// §7.9.8 — a string argument is not assignment compatible with an integral
// index type; elaboration must reject the traversal call. The int result is
// captured in an int variable so the only type conflict elaboration can see is
// the string argument against the int index type -- isolating this rule from
// any return-value assignment check.
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

// §7.9.8 — an integral argument is not assignment compatible with a string
// index type; elaboration must reject the traversal call.
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

// §7.9.8 — the assignment-compatibility rule applies to every traversal method,
// not just first()/last(); next() with a mismatched argument is also rejected.
// The int result is captured in an int variable so the sole type conflict is
// the string argument against the int index type.
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

// §7.9.8 — likewise prev() with a mismatched argument is rejected.
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

// §7.9.8 — the rule applies wherever a traversal call appears, not only on the
// right-hand side of an assignment. Here the call sits in an if condition (the
// same position the clause's own do/while traversal examples use); its integral
// result is a valid boolean, so the only conflict elaboration can flag is the
// string argument against the int index type.
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

// §7.9.8 requires a traversal method's argument to be assignment compatible
// with the associative array's index type, and conditions the rule on the two
// types rather than on the statement the call is written in.
// WalkStmtsForTraversalArgType wrote out six of the thirteen statement links
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h states, so
// each source below elaborated clean while the same `status = aa.first(s);`
// one level up was reported. The seven cases write it in the seven links the
// walk did not read.
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

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...` and
// A.6.2 gives `variable_assignment ::= variable_lvalue = expression`, so a
// traversal call may stand in the expression of a for-loop initialization.
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

// A.6.8 gives `for_step_assignment ::= operator_assignment | ...`.
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

// A.6.10 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, which is Stmt::assert_pass_stmt here and
// Stmt::assert_fail_stmt below.
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

// §18.16 and A.6.7 give `randcase_item ::= expression : statement_or_null`.
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

// §18.17 and A.6.12 give `rs_code_block ::= { { data_declaration } {
// statement_or_null } }`.
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
