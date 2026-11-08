#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

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

TEST(LoopSyntaxParsing, ForOmittedForInitialization) {
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

TEST(LoopSyntaxParsing, ForOmittedForStep) {
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
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got identifier", 3, "12.7.1"));
}

TEST(LoopSyntaxParsing, ErrorForMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++ x = i;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ')', got identifier", 3, "12.7.1"));
}

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

TEST(LoopSyntaxParsing, ForeverLoopWithAssignmentBody) {
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

TEST(LoopSyntaxParsing, RepeatLoopWithAssignmentBody) {
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

TEST(LoopSyntaxParsing, WhileLoopWithAssignmentBody) {
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

TEST(LoopSyntaxParsing, ErrorDoWhileMissingWhile) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    do x = x + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'while', got 'end'", 4, "12.7.5"));
}

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

TEST(LoopSyntaxParsing, ErrorRepeatMissingParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    repeat 8 x = x + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '(', got integer literal", 3, "12.7.2"));
}

TEST(LoopSyntaxParsing, ErrorWhileMissingParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    while x < 10 x = x + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '(', got identifier", 3, "12.7.4"));
}

TEST(LoopSyntaxParsing, ErrorForeachMissingBrackets) {
  auto r = Parse(
      "module m;\n"
      "  int arr [0:7];\n"
      "  initial begin\n"
      "    foreach (arr) arr[0] = 0;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '[', got ')'", 4, "12.7.3"));
}

TEST(LoopSyntaxParsing, ErrorForInitializationWithoutAssignmentRejected) {
  auto r = Parse(
      "module m;\n"
      "  int i;\n"
      "  initial begin\n"
      "    for (i; i < 4; i++) ;\n"
      "    for (i <= 0; i < 4; i++) ;\n"
      "    for (int j; j < 4; j++) ;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a for loop's initialization is a list of variable assignments",
      4, "A.6.8"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a for loop's initialization is a list of variable assignments",
      5, "A.6.8"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a for loop's variable declaration is written 'data_type", 6,
      "A.6.8"));
}

TEST(LoopSyntaxParsing, ErrorForStepOutsideItsThreeFormsRejected) {
  auto r = Parse(
      "module m;\n"
      "  int i;\n"
      "  initial begin\n"
      "    for (i = 0; i < 4; bump, obj.advance) ;\n"
      "    for (i = 0; i < 4; i + 1) ;\n"
      "    for (i = 0; i < 4; i <= i + 1) ;\n"
      "    for (i = 0; i < 4; i++, i += 2, next(i), $urandom()) ;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(ReportedError(
      r.diags, "a for loop's step is an operator assignment", 4, "A.6.8"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a for loop's step is an operator assignment", 5, "A.6.8"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a for loop's step is an operator assignment", 6, "A.6.8"));
  EXPECT_FALSE(ReportedError(
      r.diags, "a for loop's step is an operator assignment", 7, "A.6.8"));
}

TEST(LoopSyntaxParsing, ErrorForeachNullBodyRejected) {
  auto r = Parse(
      "module m;\n"
      "  int arr [0:7];\n"
      "  initial foreach (arr[i]) ;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a foreach loop's body is a statement; ';' alone is none", 3,
      "A.6.8"));
}

TEST(LoopSyntaxParsing, ForeachScopedAndClassHandleArrayId) {
  auto r = Parse(
      "class C;\n"
      "  int arr [4];\n"
      "  static int tab [4];\n"
      "  function void f();\n"
      "    foreach (this.arr[i]) arr[i] = i;\n"
      "    foreach (C::tab[i]) tab[i] = i;\n"
      "    foreach (pkg::mem[i]) arr[0] = i;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* method = r.cu->classes[0]->members[2]->method;
  ASSERT_NE(method, nullptr);
  const auto& loops = method->func_body_stmts;
  ASSERT_EQ(loops.size(), 3u);
  for (auto* loop : loops) {
    ASSERT_EQ(loop->kind, StmtKind::kForeach);
    ASSERT_NE(loop->expr, nullptr);
    EXPECT_EQ(loop->expr->kind, ExprKind::kMemberAccess);
    ASSERT_NE(loop->expr->rhs, nullptr);
  }
  EXPECT_EQ(loops[0]->expr->lhs->text, "this");
  EXPECT_EQ(loops[0]->expr->rhs->text, "arr");
  EXPECT_TRUE(loops[1]->expr->is_scope_resolution);
  EXPECT_EQ(loops[1]->expr->rhs->text, "tab");
  EXPECT_TRUE(loops[2]->expr->is_scope_resolution);
  EXPECT_EQ(loops[2]->expr->lhs->text, "pkg");
}

TEST(LoopSyntaxParsing, ForVariableOfATypeReference) {
  auto r = Parse(
      "module m;\n"
      "  int x, s;\n"
      "  initial begin\n"
      "    for (var type(x) i = -2; i < 1; i++) s += i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->for_init_types.size(), 1u);
  EXPECT_NE(stmt->for_init_types[0].type_ref_expr, nullptr);
}

TEST(LoopSyntaxParsing, ForVariableOfATypeReferenceWithoutVarIsReported) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial for (type(x) j = 0; j < 1; j++) ;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "type_reference in a variable declaration must be "
                            "preceded by the 'var' keyword",
                            3, "6.23"));
}

TEST(LoopSyntaxParsing, AForeachArraySelectsBitsBeforeAPeriod) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    foreach (s[1:0].m[i]) begin end\n"
      "    foreach (s[0+:2].m[i]) begin end\n"
      "    foreach (s[1].m[i]) begin end\n"
      "    foreach (s[1][2].m[i]) begin end\n"
      "  end\n"
      "endmodule\n");
  for (uint32_t line : {3u, 4u}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "a foreach array is a hierarchical identifier, "
                              "whose selects before a period are bit-selects",
                              line, "A.6.8"))
        << "line " << line;
  }
  EXPECT_EQ(r.diags.size(), 2u);
}

}  // namespace
