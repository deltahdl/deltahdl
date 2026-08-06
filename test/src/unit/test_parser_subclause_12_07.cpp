// §12.7 Loop statements — head clause. The head owns Syntax 12-5: the single
// loop_statement production with its six alternatives, plus the for-family
// subproductions (for_initialization, for_variable_declaration, for_step,
// for_step_assignment) and loop_variables. The per-loop semantics live in the
// descendant subclauses §12.7.1–§12.7.6 and are tested in their own files.
// These tests observe the parser building the Syntax 12-5 grammar into the AST.
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// Syntax 12-5: loop_statement offers exactly six looping constructs. A single
// procedural block using all six forms must dispatch each to its own StmtKind.
TEST(LoopStatementSyntax, SixLoopAlternatives) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    forever break;\n"
      "    repeat (3) x = 1;\n"
      "    while (c) x = 2;\n"
      "    for (int i = 0; i < 3; i++) x = 3;\n"
      "    do x = 4; while (c);\n"
      "    foreach (arr[j]) x = 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto stmts = AllInitialStmts(r);
  ASSERT_EQ(stmts.size(), 6u);
  EXPECT_EQ(stmts[0]->kind, StmtKind::kForever);
  EXPECT_EQ(stmts[1]->kind, StmtKind::kRepeat);
  EXPECT_EQ(stmts[2]->kind, StmtKind::kWhile);
  EXPECT_EQ(stmts[3]->kind, StmtKind::kFor);
  EXPECT_EQ(stmts[4]->kind, StmtKind::kDoWhile);
  EXPECT_EQ(stmts[5]->kind, StmtKind::kForeach);
}

// for_initialization ::= list_of_variable_assignments | ...
// The plain-assignment alternative yields blocking assignments whose init
// slots carry no declared data type (implicit).
TEST(LoopStatementSyntax, ForInitializationAssignmentsForm) {
  auto r = Parse(
      "module m;\n"
      "  integer i, j;\n"
      "  initial\n"
      "    for (i = 0, j = 10; i < j; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_EQ(stmt->for_inits.size(), 2u);
  EXPECT_EQ(stmt->for_inits[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->for_inits[1]->kind, StmtKind::kBlockingAssign);
  ASSERT_EQ(stmt->for_init_types.size(), 2u);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kImplicit);
  EXPECT_EQ(stmt->for_init_types[1].kind, DataTypeKind::kImplicit);
}

// for_initialization ::= ... | for_variable_declaration { , ... }
// The declaring alternative attaches a real data type to the init slot.
TEST(LoopStatementSyntax, ForInitializationDeclarationForm) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (int i = 0; i < 3; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->for_init_types.size(), 1u);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kInt);
  ASSERT_EQ(stmt->for_inits.size(), 1u);
  EXPECT_EQ(stmt->for_inits[0]->kind, StmtKind::kBlockingAssign);
}

// for_initialization ::= for_variable_declaration { , for_variable_declaration
// } The repetition alternative lets each comma-separated declaration carry its
// own data type (distinct from the single-type continuation form below), so
// both init slots record a concrete declared type.
TEST(LoopStatementSyntax, ForInitializationMultipleDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (int i = 0, int j = 4; i < j; i++, j--) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_EQ(stmt->for_inits.size(), 2u);
  ASSERT_EQ(stmt->for_init_types.size(), 2u);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kInt);
  EXPECT_EQ(stmt->for_init_types[1].kind, DataTypeKind::kInt);
}

// for_variable_declaration ::= [ var ] data_type variable_identifier = ...
// The optional var keyword prefix is accepted and does not change the parsed
// data type of the declared control variable.
TEST(LoopStatementSyntax, ForVariableDeclarationVarKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (var int i = 0; i < 3; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->for_init_types.size(), 1u);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kInt);
}

// for_variable_declaration ::= ... = expression { , variable_identifier =
// expression }. A single data type may be followed by several
// variable_identifier = expression pairs (no data type repeated), and a later
// initializer may reference an earlier control variable.
TEST(LoopStatementSyntax, ForVariableDeclarationContinuationForm) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (int i = 0, j = i + 3; i < j; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_EQ(stmt->for_inits.size(), 2u);
  EXPECT_EQ(stmt->for_inits[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->for_inits[1]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kInt);
}

// for_step_assignment ::= operator_assignment | inc_or_dec_expression |
// function_subroutine_call. All three forms are accepted, comma-separated.
TEST(LoopStatementSyntax, ForStepThreeAlternatives) {
  auto r = Parse(
      "module m;\n"
      "  function void step(); endfunction\n"
      "  initial\n"
      "    for (i = 0; i < 3; i += 1, i++, step()) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->for_steps.size(), 3u);
  // operator_assignment (compound += lowers to a blocking assignment).
  EXPECT_EQ(stmt->for_steps[0]->kind, StmtKind::kBlockingAssign);
  // inc_or_dec_expression.
  EXPECT_EQ(stmt->for_steps[1]->kind, StmtKind::kExprStmt);
  // function_subroutine_call.
  EXPECT_EQ(stmt->for_steps[2]->kind, StmtKind::kExprStmt);
  EXPECT_EQ(stmt->for_steps[2]->expr->kind, ExprKind::kCall);
}

// loop_variables ::= [ index_variable_identifier ] { , [ index_variable_
// identifier ] }. An index slot may be omitted, leaving an empty entry that
// still holds a place in the dimension list.
TEST(LoopStatementSyntax, LoopVariablesOmittedSlot) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    foreach (arr[, j]) x = j;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
  EXPECT_TRUE(stmt->foreach_vars[0].empty());
  EXPECT_EQ(stmt->foreach_vars[1], "j");
}

// loop_variables — every index present across multiple dimensions exercises the
// { , index_variable_identifier } repetition with named entries.
TEST(LoopStatementSyntax, LoopVariablesAllNamed) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    foreach (m[i, j]) x = i + j;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
  EXPECT_EQ(stmt->foreach_vars[1], "j");
}

// loop_variables — a trailing comma leaves the final index slot empty, the
// mirror of the leading-omission form above.
TEST(LoopStatementSyntax, LoopVariablesTrailingOmitted) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    foreach (arr[i, ]) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
  EXPECT_TRUE(stmt->foreach_vars[1].empty());
}

// loop_statement for-alternative: the [ for_initialization ] clause is
// optional. Omitting it leaves the init list empty while the other clauses are
// retained.
TEST(LoopStatementSyntax, ForInitializationClauseOmitted) {
  auto r = Parse(
      "module m;\n"
      "  integer i;\n"
      "  initial\n"
      "    for (; i < 3; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_TRUE(stmt->for_inits.empty());
  EXPECT_NE(stmt->for_cond, nullptr);
  ASSERT_EQ(stmt->for_steps.size(), 1u);
}

// loop_statement for-alternative: the [ expression ] condition clause is
// optional; omitting it yields a null condition.
TEST(LoopStatementSyntax, ForConditionClauseOmitted) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (int i = 0;; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_EQ(stmt->for_inits.size(), 1u);
  EXPECT_EQ(stmt->for_cond, nullptr);
}

// loop_statement for-alternative: the [ for_step ] clause is optional; omitting
// it leaves the step list empty while init and condition remain.
TEST(LoopStatementSyntax, ForStepClauseOmitted) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (int i = 0; i < 3;) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_cond, nullptr);
  EXPECT_TRUE(stmt->for_steps.empty());
}

// loop_statement for-alternative: all three clauses may be omitted at once,
// producing an unconditional loop with empty init, null condition, empty step.
TEST(LoopStatementSyntax, ForAllClausesOmitted) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (;;) x = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_TRUE(stmt->for_inits.empty());
  EXPECT_EQ(stmt->for_cond, nullptr);
  EXPECT_TRUE(stmt->for_steps.empty());
}

// loop_statement: the body of forever/repeat/while/for/do is statement_or_null,
// so a bare null statement (;) is an accepted loop body.
TEST(LoopStatementSyntax, LoopBodyNullStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    while (c) ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kNull);
}

// for_variable_declaration data_type admits a 4-state packed vector, not only a
// plain int; the declared type is recorded on the init slot.
TEST(LoopStatementSyntax, ForVariableDeclarationVectorType) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (logic [7:0] i = 0; i < 8; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->for_init_types.size(), 1u);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kLogic);
}

// for_variable_declaration data_type also admits a 2-state scalar type.
TEST(LoopStatementSyntax, ForVariableDeclarationBitType) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (bit i = 0; i < 1; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->for_init_types.size(), 1u);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kBit);
}

// for_variable_declaration data_type admits a user-defined (named) type. The
// typedef is introduced with real source syntax so the parser knows the name is
// a type; the for-init must then be recognized as a declaration (not a plain
// assignment) and record the named type.
TEST(LoopStatementSyntax, ForVariableDeclarationNamedType) {
  auto r = Parse(
      "module m;\n"
      "  typedef int my_t;\n"
      "  initial\n"
      "    for (my_t i = 0; i < 3; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_EQ(stmt->for_init_types.size(), 1u);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kNamed);
  EXPECT_EQ(stmt->for_init_types[0].type_name, "my_t");
  ASSERT_EQ(stmt->for_inits.size(), 1u);
  EXPECT_EQ(stmt->for_inits[0]->kind, StmtKind::kBlockingAssign);
}

// NEGATIVE — repeat requires its expression to be parenthesized.
TEST(LoopStatementSyntax, RepeatRequiresParenthesizedExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    repeat 3 x = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// NEGATIVE — while requires its control expression to be parenthesized.
TEST(LoopStatementSyntax, WhileRequiresParenthesizedExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    while c x = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// NEGATIVE — foreach requires its array reference and loop_variables to be
// enclosed in parentheses.
TEST(LoopStatementSyntax, ForeachRequiresParentheses) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    foreach arr[i] x = i;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// NEGATIVE — the for header requires both clause-separating semicolons; a
// missing separator after the initialization is rejected.
TEST(LoopStatementSyntax, ForRequiresClauseSemicolons) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (int i = 0 i < 3; i++) x = i;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// NEGATIVE — the do...while form requires the while keyword after the body.
TEST(LoopStatementSyntax, DoWhileRequiresWhileKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    do x = 1; y = 2;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
