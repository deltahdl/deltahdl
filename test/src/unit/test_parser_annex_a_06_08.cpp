#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt *FirstInitialStmt(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock)
      continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

} // namespace

// =============================================================================
// A.6.8 Looping statements — loop_statement
// =============================================================================

// --- forever statement_or_null ---

TEST(ParserA608, ForeverLoop) {
  auto r = Parse("module m;\n"
                 "  initial begin forever #5 clk = ~clk; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserA608, ForeverNullStmt) {
  auto r = Parse("module m;\n"
                 "  initial begin forever ; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
}

// --- repeat ( expression ) statement_or_null ---

TEST(ParserA608, RepeatLoop) {
  auto r = Parse("module m;\n"
                 "  initial begin repeat (10) @(posedge clk); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
  EXPECT_NE(stmt->condition, nullptr);
}

TEST(ParserA608, RepeatNullStmt) {
  auto r = Parse("module m;\n"
                 "  initial begin repeat (5) ; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
}

// --- while ( expression ) statement_or_null ---

TEST(ParserA608, WhileLoop) {
  auto r = Parse("module m;\n"
                 "  initial begin while (x > 0) x = x - 1; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserA608, WhileNullStmt) {
  auto r = Parse("module m;\n"
                 "  initial begin while (x > 0) ; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
}

// --- for ( [for_initialization] ; [expression] ; [for_step] ) stmt_or_null ---

TEST(ParserA608, ForLoopParse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 10; i++) x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
}

TEST(ParserA608, ForLoopParts) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 10; i++) x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->for_init, nullptr);
  EXPECT_NE(stmt->for_cond, nullptr);
  EXPECT_NE(stmt->for_step, nullptr);
  EXPECT_NE(stmt->for_body, nullptr);
}

TEST(ParserA608, ForLoopTypedInit) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 10; i++) x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kInt);
}

TEST(ParserA608, ForLoopUntypedInit) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    for (i = 0; i < 10; i++) x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kImplicit);
}

// §A.6.8: for_initialization is optional — empty init
TEST(ParserA608, ForEmptyInit) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    for (; i < 10; i++) x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init, nullptr);
}

// §A.6.8: expression in for condition is optional — empty cond
TEST(ParserA608, ForEmptyCond) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    for (int i = 0; ; i++) begin\n"
                 "      if (i == 10) break;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_cond, nullptr);
}

// §A.6.8: for_step is optional — empty step
TEST(ParserA608, ForEmptyStep) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 10;) begin\n"
                 "      i = i + 1;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_step, nullptr);
}

// §A.6.8: all three for parts optional — for (;;)
TEST(ParserA608, ForAllEmpty) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    for (;;) break;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init, nullptr);
  EXPECT_EQ(stmt->for_cond, nullptr);
  EXPECT_EQ(stmt->for_step, nullptr);
}

TEST(ParserA608, ForNullStmt) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 10; i++) ;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
}

// --- for_variable_declaration: [var] data_type variable_identifier = expr ---

TEST(ParserA608, ForVarKeyword) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    for (var int i = 0; i < 10; i++) x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kInt);
}

TEST(ParserA608, ForLogicTypeInit) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    for (logic [7:0] i = 0; i < 10; i++) x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kLogic);
}

// --- for_step_assignment: operator_assignment ---

TEST(ParserA608, ForStepCompoundAssign) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 10; i += 1) x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_step, nullptr);
}

// --- for_step_assignment: inc_or_dec_expression ---

TEST(ParserA608, ForStepPostIncrement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 10; i++) x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->for_step, nullptr);
}

TEST(ParserA608, ForStepPreIncrement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 10; ++i) x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->for_step, nullptr);
}

TEST(ParserA608, ForStepPostDecrement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    for (int i = 10; i > 0; i--) x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->for_step, nullptr);
}

// --- do statement_or_null while ( expression ) ; ---

TEST(ParserA608, DoWhileLoop) {
  auto r = Parse("module m;\n"
                 "  initial begin do x = x - 1; while (x > 0); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserA608, DoWhileNullStmt) {
  auto r = Parse("module m;\n"
                 "  initial begin do ; while (x > 0); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
}

TEST(ParserA608, DoWhileBlockBody) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    do begin x = x + 1; end while (x < 10);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

// --- foreach ( ps_or_hierarchical_array_identifier [loop_variables] ) stmt ---

TEST(ParserA608, ForeachStmt) {
  auto r = Parse("module m;\n"
                 "  initial begin foreach (arr[i]) $display(arr[i]); end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_NE(stmt->expr, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserA608, ForeachSingleVar) {
  auto r = Parse("module m;\n"
                 "  initial begin foreach (arr[i]) x = i; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->foreach_vars.size(), 1u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
}

// §A.6.8: loop_variables — multiple comma-separated identifiers
TEST(ParserA608, ForeachMultipleVars) {
  auto r = Parse("module m;\n"
                 "  initial begin foreach (matrix[i, j]) x = i; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
  EXPECT_EQ(stmt->foreach_vars[1], "j");
}

// §A.6.8: loop_variables — empty slots (skipped dimensions)
TEST(ParserA608, ForeachEmptyVarSlot) {
  auto r = Parse("module m;\n"
                 "  initial begin foreach (arr[, j]) x = j; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
  EXPECT_TRUE(stmt->foreach_vars[0].empty());
  EXPECT_EQ(stmt->foreach_vars[1], "j");
}

// §A.6.8: ps_or_hierarchical_array_identifier — hierarchical name
TEST(ParserA608, ForeachHierarchicalArray) {
  auto r = Parse("module m;\n"
                 "  initial begin foreach (obj.arr[i]) x = i; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kMemberAccess);
}

TEST(ParserA608, ForeachBlockBody) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    foreach (arr[i]) begin\n"
                 "      x = arr[i];\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}
