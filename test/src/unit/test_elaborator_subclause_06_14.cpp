#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast.h"

using namespace delta;

namespace {

TEST(ChandleDataType, ChandleWidth64) {
  DataType dt;
  dt.kind = DataTypeKind::kChandle;
  EXPECT_EQ(EvalTypeWidth(dt), 64u);
}

TEST(ChandleDataType, ChandleNotIntegral) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kChandle));
}

TEST(ChandleDataType, ChandleNot4State) {
  EXPECT_FALSE(Is4stateType(DataTypeKind::kChandle));
}

TEST(ChandleDataType, ChandlePort_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top(input chandle ch);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot be used as a port type", 1,
                            "6.14"));
}

TEST(ChandleDataType, ChandleContAssign_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot be used in continuous assignment",
                            3, "6.14"));
}

TEST(ChandleDataType, ChandleSensitivity_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle ch;\n"
      "  always @(ch) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot appear in event expression", 3,
                            "6.14"));
}

TEST(ChandleDataType, ChandleIsChandle) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle ch;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_chandle);
}

TEST(ChandleDataType, ChandleToChandleAssign_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleAssignNull_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  initial h = null;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleOutputPort_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top(output chandle ch);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot be used as a port type", 1,
                            "6.14"));
}

TEST(ChandleDataType, ChandleInoutPort_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top(inout chandle ch);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot be used as a port type", 1,
                            "6.14"));
}

// The rule §6.14 states here is reported under the clause that states the
// obligation, §7.3.2 ("Dynamic types and chandle types shall not be used in
// untagged unions"), and stands at the `typedef` keyword.
TEST(ChandleDataType, ChandleInUntaggedUnion_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef union { chandle ch; int i; } my_union;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle type can only be used in tagged unions", 2,
                            "7.3.2"));
}

TEST(ChandleDataType, ChandleInTaggedUnion_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef union tagged { chandle Ch; int I; } my_union;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleInsertedIntoAssociativeArray_Ok) {
  // §6.14: a chandle may be inserted into an associative array. Declaring a
  // chandle-valued associative array and inserting a null handle at a key must
  // elaborate without error -- the chandle usage restrictions (ports, packed
  // types, untagged unions, ...) do not extend to associative-array elements.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle aa[int];\n"
      "  initial aa[3] = null;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleAssociativeArrayElementRead_Ok) {
  // §6.14: a chandle may be inserted into an associative array, and reading an
  // element back with an index is a legal element access -- not a bit-select of
  // a scalar chandle. Reading aa[key] into another chandle must not be
  // rejected.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle aa[int];\n"
      "  chandle x;\n"
      "  initial x = aa[3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleAssociativeArrayElementWrite_Ok) {
  // §6.14: "Chandles can be inserted into associative arrays", and the handle
  // inserted may come from a chandle variable rather than being the null the
  // insertion test above uses. Writing one into an element is an assignment
  // between two chandles, so neither the "assigned to variables of any other
  // type" prohibition nor the "only from another chandle" rule is violated.
  // This is the write counterpart of the element read above.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle aa[int];\n"
      "  chandle x;\n"
      "  initial aa[3] = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleScalarBitSelect_Error) {
  // §6.14: a chandle is not a vector, so bit-selecting a scalar chandle is
  // still illegal. This is the negative counterpart to the associative-array
  // element access above -- the array base is what makes the index legal, not
  // chandle. The lvalue is a chandle, so the assign-to-other-type rule is not
  // what fires; the "only from another chandle or null" rule reports at the
  // same line, and naming the bit-select report is what tells the two apart.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  chandle x;\n"
      "  initial x = h[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select on chandle is illegal", 4, "6.14"));
}

// A chandle member of a packed structure is reported by the §7.2.1
// packed-member-type rule, which names the member, and stands at the `typedef`
// keyword.
TEST(ChandleDataType, ChandleInPackedStruct_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed { chandle ch; int i; } my_struct;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type of member 'ch' is not allowed in a packed structure", 2, "7.2.1"));
}

TEST(ChandleDataType, ChandleAssignToInt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int x;\n"
      "  initial x = h;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot be assigned to a non-chandle "
                            "variable",
                            4, "6.14"));
}

TEST(ChandleDataType, IntAssignToChandle_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int x;\n"
      "  initial h = x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle can only be assigned from another chandle "
                            "or null",
                            4, "6.14"));
}

TEST(ChandleDataType, ChandleAddition_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial r = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleBitwiseOr_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a;\n"
      "  int r;\n"
      "  initial r = a | 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleUnaryNot_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int r;\n"
      "  initial r = ~h;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleRelational_Error) {
  // §6.14: only equality/inequality operators are valid on chandles; a
  // relational operator such as < is not in the permitted set.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial r = (a < b) ? 1 : 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleEqualityOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial r = (a == b) ? 1 : 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleInequalityOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int r;\n"
      "  initial r = (h != null) ? 1 : 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleCaseEqualityOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int r;\n"
      "  initial r = (h === null) ? 1 : 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleCaseInequalityOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int r;\n"
      "  initial r = (h !== null) ? 1 : 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.14 states the operations a chandle admits -- the equality family, and no
// bit-select of a scalar chandle -- and names no statement those rules are
// suspended in. Elaborator::WalkStmtsForChandleOps in
// src/elaborator/elaborator_validate_datatype_ops.cpp had written out six of
// the thirteen child-statement links Stmt declares, so the addition of
// ChandleAddition_Error above elaborated clean in any of the other seven. The
// walk now takes its list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h, and each case below rewrites
// that addition in one newly reached position.

// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword`, whose
// statements the parser keeps in Stmt::fork_stmts.
TEST(ChandleDataType, ChandleAdditionInForkArm_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial fork\n"
      "    r = a + b;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 5, "6.14"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...` and
// `variable_assignment ::= variable_lvalue = expression`, so an assignment
// whose right-hand side adds two chandles stands in a for-loop header. The
// parser keeps it in Stmt::for_inits.
TEST(ChandleDataType, ChandleAdditionInForInitialization_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial for (r = a + b; r < 1; r = r + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, and an
// operator_assignment written with `=` carries an arbitrary expression. The
// parser keeps it in Stmt::for_steps.
TEST(ChandleDataType, ChandleAdditionInForStep_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial for (r = 0; r < 1; r = a + b) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

// A.6.10 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion (§16.3) holds a statement in
// each arm, kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This
// case and the next cover one arm each.
TEST(ChandleDataType, ChandleAdditionInAssertionPassStatement_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial assert (1) r = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleAdditionInAssertionFailStatement_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial assert (1) else r = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second of each Stmt::randcase_items pair.
TEST(ChandleDataType, ChandleAdditionInRandcaseItem_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial randcase\n"
      "    1 : r = a + b;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 5, "6.14"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block (§18.17) holds ordinary
// procedural statements. The parser keeps them in RsProd::code_stmts, reached
// through Stmt::rs_productions and through no other member of Stmt.
TEST(ChandleDataType, ChandleAdditionInRandsequenceCodeBlock_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { r = a + b; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 6, "6.14"));
}

}  // namespace
