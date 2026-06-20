#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(LoopSyntaxParsing, ForLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) a[i] = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_body, nullptr);
}

TEST(LoopSyntaxParsing, ForLoopWithBlockBody) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 8; i++) begin\n"
      "      $display(\"%d\", i);\n"
      "      x = x + i;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_NE(stmt->for_body, nullptr);
  EXPECT_EQ(stmt->for_body->kind, StmtKind::kBlock);
}

TEST(LoopSyntaxParsing, ForBodyBlockingAssign) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    for (int i = 0; i < 4; i++)\n"
      "      mem[i] = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_NE(stmt->for_body, nullptr);
  EXPECT_EQ(stmt->for_body->kind, StmtKind::kBlockingAssign);
}

TEST(LoopSyntaxParsing, ForWithByteDecl) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (byte b = 0; b < 100; b = b + 1)\n"
      "      data = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kByte);
}

TEST(LoopSyntaxParsing, IfElseInsideForBody) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 16; i = i + 1) begin\n"
      "      if (i[0]) odd[i] = 1;\n"
      "      else even[i] = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_NE(stmt->for_body, nullptr);
  EXPECT_EQ(stmt->for_body->kind, StmtKind::kBlock);
  ASSERT_GE(stmt->for_body->stmts.size(), 1u);
  EXPECT_EQ(stmt->for_body->stmts[0]->kind, StmtKind::kIf);
}
static ModuleItem* FirstAlwaysLatchItem(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysLatchBlock) return item;
  }
  return nullptr;
}

TEST(LoopSyntaxParsing, ForLoopInAlwaysLatch) {
  auto r = Parse(
      "module m;\n"
      "  logic en;\n"
      "  logic [7:0] q [0:3];\n"
      "  logic [7:0] d [0:3];\n"
      "  always_latch begin\n"
      "    for (int i = 0; i < 4; i++)\n"
      "      if (en) q[i] <= d[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kFor);
  EXPECT_NE(item->body->stmts[0]->for_cond, nullptr);
  EXPECT_NE(item->body->stmts[0]->for_body, nullptr);
}

TEST(LoopSyntaxParsing, ForIntDeclHasInitAndCond) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i = i + 1) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_FALSE(stmt->for_inits.empty());
  EXPECT_NE(stmt->for_cond, nullptr);
}

TEST(LoopSyntaxParsing, ForIntDeclHasStepBodyType) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i = i + 1) x = i;\n"
      "  end\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_FALSE(stmt->for_steps.empty());
  EXPECT_NE(stmt->for_body, nullptr);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kInt);
}

TEST(LoopSyntaxParsing, ForWithLogicDecl) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (logic [7:0] i = 0; i < 10; i = i + 1) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kLogic);
}

TEST(LoopSyntaxParsing, ForIntDeclWithBlockBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i = i + 1) begin\n"
      "      $display(i);\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmtT(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kInt);
}

TEST(LoopSyntaxParsing, ForWithoutDeclStillWorks) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (i = 0; i < 10; i = i + 1) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kImplicit);
}

TEST(LoopSyntaxParsing, ForAllPartsNonNull) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_FALSE(stmt->for_inits.empty());
  EXPECT_NE(stmt->for_cond, nullptr);
  EXPECT_FALSE(stmt->for_steps.empty());
  EXPECT_NE(stmt->for_body, nullptr);
}

TEST(LoopSyntaxParsing, ForEmptyInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_TRUE(stmt->for_inits.empty());
}

TEST(LoopSyntaxParsing, ForEmptyCond) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; ; i++) begin\n"
      "      if (i == 10) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_cond, nullptr);
}

TEST(LoopSyntaxParsing, ForEmptyStep) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10;) begin\n"
      "      i = i + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_TRUE(stmt->for_steps.empty());
}

TEST(LoopSyntaxParsing, ForAllEmpty) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (;;) break;\n"
      "  end\n"
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

TEST(LoopSyntaxParsing, ForNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
}

TEST(LoopSyntaxParsing, ForVarKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (var int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kInt);
}

TEST(LoopSyntaxParsing, ForStepCompoundAssign) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i += 1) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_FALSE(stmt->for_steps.empty());
}

TEST(LoopSyntaxParsing, ForStepPostIncrement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_FALSE(stmt->for_steps.empty());
}

TEST(LoopSyntaxParsing, ForStepPreIncrement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; ++i) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_FALSE(stmt->for_steps.empty());
}

TEST(LoopSyntaxParsing, ForStepPostDecrement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 10; i > 0; i--) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_FALSE(stmt->for_steps.empty());
}
TEST(LoopSyntaxParsing, ForWithArrayBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 8; i++)\n"
      "      data[i] = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_cond, nullptr);
  EXPECT_NE(stmt->for_body, nullptr);
}

static ModuleItem* FirstFuncOrTask(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl)
      return item;
  }
  return nullptr;
}

static Stmt* FindStmtByKind(ModuleItem* item, StmtKind kind) {
  for (auto* stmt : item->func_body_stmts) {
    if (stmt->kind == kind) return stmt;
  }
  return nullptr;
}

TEST(LoopSyntaxParsing, ForLoopInitInStaticFunc) {
  auto r = Parse(
      "module m;\n"
      "  function static int sum_n(int n);\n"
      "    int total;\n"
      "    total = 0;\n"
      "    for (int i = 0; i < n; i = i + 1)\n"
      "      total = total + i;\n"
      "    return total;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  EXPECT_TRUE(fn->is_static);
  auto* for_stmt = FindStmtByKind(fn, StmtKind::kFor);
  ASSERT_NE(for_stmt, nullptr);
  EXPECT_EQ(for_stmt->for_init_types[0].kind, DataTypeKind::kInt);
}

TEST(LoopSyntaxParsing, ForLoopInitInAutoFunc) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int sum_auto(int n);\n"
      "    int total = 0;\n"
      "    for (int i = 0; i < n; i = i + 1)\n"
      "      total = total + i;\n"
      "    return total;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  EXPECT_TRUE(fn->is_automatic);
  auto* for_stmt = FindStmtByKind(fn, StmtKind::kFor);
  ASSERT_NE(for_stmt, nullptr);
  EXPECT_EQ(for_stmt->for_init_types[0].kind, DataTypeKind::kInt);
}

TEST(LoopSyntaxParsing, ForStepPreDecrement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 10; i > 0; --i) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_FALSE(stmt->for_steps.empty());
}

TEST(LoopSyntaxParsing, ForStepFunctionCall) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i = next_val(i)) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_FALSE(stmt->for_steps.empty());
}

// for_step_assignment ::= ... | function_subroutine_call — a bare call as the
// step, distinct from an operator_assignment whose right side happens to call a
// function. It parses to a plain expression statement.
TEST(LoopSyntaxParsing, ForStepStandaloneSubroutineCall) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; advance(i)) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_EQ(stmt->for_steps.size(), 1u);
  EXPECT_EQ(stmt->for_steps[0]->kind, StmtKind::kExprStmt);
  EXPECT_NE(stmt->for_steps[0]->expr, nullptr);
}

TEST(LoopSyntaxParsing, ForVarLogicTypeDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (var logic [7:0] i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kLogic);
}

TEST(LoopSyntaxParsing, ErrorForMissingSemicolonAfterInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0 i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LoopSyntaxParsing, ErrorForMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++ x = i;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// loop_statement ::= for ... — for_initialization may declare more than one
// control variable (for_variable_declaration { , for_variable_declaration }).
TEST(LoopSyntaxParsing, ForInitMultipleDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0, j = 9; i < j; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_inits.size(), 2u);
}

// for_initialization ::= list_of_variable_assignments — the comma-separated
// form without local declarations.
TEST(LoopSyntaxParsing, ForInitListOfVariableAssignments) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (i = 0, j = 9; i < j; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_inits.size(), 2u);
}

// for_step ::= for_step_assignment { , for_step_assignment } — more than one
// step assignment separated by commas.
TEST(LoopSyntaxParsing, ForStepMultipleAssignments) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0, j = 9; i < j; i++, j--) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_steps.size(), 2u);
}

// loop_statement ::= forever statement_or_null
TEST(LoopSyntaxParsing, ForeverLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    forever x = x + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
  EXPECT_NE(stmt->body, nullptr);
}

// loop_statement ::= repeat ( expression ) statement_or_null
TEST(LoopSyntaxParsing, RepeatLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    repeat (8) x = x + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

// loop_statement ::= while ( expression ) statement_or_null
TEST(LoopSyntaxParsing, WhileLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    while (x < 10) x = x + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

// loop_statement ::= do statement_or_null while ( expression ) ;
TEST(LoopSyntaxParsing, DoWhileLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    do x = x + 1; while (x < 10);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

// The do-while body must be followed by 'while ( expr ) ;'.
TEST(LoopSyntaxParsing, ErrorDoWhileMissingWhile) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    do x = x + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// loop_statement ::= foreach ( ps_or_hierarchical_array_identifier
//                               [ loop_variables ] ) statement
TEST(LoopSyntaxParsing, ForeachLoop) {
  auto r = Parse(
      "module m;\n"
      "  int arr [0:7];\n"
      "  initial begin\n"
      "    foreach (arr[i]) arr[i] = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_NE(stmt->expr, nullptr);
  ASSERT_EQ(stmt->foreach_vars.size(), 1u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
  EXPECT_NE(stmt->body, nullptr);
}

// foreach with more than one loop variable for a multidimensional array.
TEST(LoopSyntaxParsing, ForeachMultipleLoopVars) {
  auto r = Parse(
      "module m;\n"
      "  int mat [0:3][0:3];\n"
      "  initial begin\n"
      "    foreach (mat[i, j]) mat[i][j] = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_EQ(stmt->foreach_vars.size(), 2u);
}

// The foreach array reference may be a hierarchical (member) name, exercising
// the ps_or_hierarchical_array_identifier slot of the foreach alternative.
TEST(LoopSyntaxParsing, ForeachHierarchicalArrayId) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    foreach (pkt.data[i]) pkt.data[i] = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kMemberAccess);
  ASSERT_EQ(stmt->foreach_vars.size(), 1u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
}

// repeat ( expression ) — the parentheses around the count are required.
TEST(LoopSyntaxParsing, ErrorRepeatMissingParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    repeat 8 x = x + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// while ( expression ) — the parentheses around the condition are required.
TEST(LoopSyntaxParsing, ErrorWhileMissingParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    while x < 10 x = x + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// foreach ( array [ loop_variables ] ) — the bracketed loop-variable list is
// part of the syntax; omitting the brackets is an error.
TEST(LoopSyntaxParsing, ErrorForeachMissingBrackets) {
  auto r = Parse(
      "module m;\n"
      "  int arr [0:7];\n"
      "  initial begin\n"
      "    foreach (arr) arr[0] = 0;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
