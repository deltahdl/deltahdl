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

// Helpers to extract items from the first module.
static ModuleItem *FindItem(const std::vector<ModuleItem *> &items,
                            ModuleItemKind kind) {
  for (auto *item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

static std::vector<ModuleItem *> FindItems(
    const std::vector<ModuleItem *> &items, ModuleItemKind kind) {
  std::vector<ModuleItem *> result;
  for (auto *item : items) {
    if (item->kind == kind) result.push_back(item);
  }
  return result;
}

// Return the first statement inside the first initial block's begin/end.
static Stmt *FirstInitialStmt(ParseResult &r) {
  auto *item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  if (!item || !item->body) return nullptr;
  if (item->body->kind == StmtKind::kBlock) {
    return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
  }
  return item->body;
}

}  // namespace

// =============================================================================
// A.6.2 Production: initial_construct
// initial_construct ::= initial statement_or_null
// =============================================================================

TEST(ParserA602, InitialConstruct_SingleStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"hello\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
}

TEST(ParserA602, InitialConstruct_BeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

TEST(ParserA602, InitialConstruct_NullStmt) {
  // initial with null statement (just a semicolon)
  auto r = Parse(
      "module m;\n"
      "  initial ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kNull);
}

TEST(ParserA602, InitialConstruct_Multiple) {
  // Multiple initial blocks in the same module
  auto r = Parse(
      "module m;\n"
      "  initial a = 0;\n"
      "  initial b = 0;\n"
      "  initial c = 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto inits =
      FindItems(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  EXPECT_EQ(inits.size(), 3u);
}

// =============================================================================
// A.6.2 Production: always_construct
// always_construct ::= always_keyword statement
// =============================================================================

TEST(ParserA602, AlwaysConstruct_PlainAlways) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  ASSERT_NE(item->body, nullptr);
}

TEST(ParserA602, AlwaysConstruct_AlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  always_comb y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
}

TEST(ParserA602, AlwaysConstruct_AlwaysFF) {
  auto r = Parse(
      "module m;\n"
      "  always_ff @(posedge clk or negedge rst_n)\n"
      "    if (!rst_n) q <= 0;\n"
      "    else q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  // Sensitivity list should contain posedge clk and negedge rst_n
  EXPECT_EQ(item->sensitivity.size(), 2u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_EQ(item->sensitivity[1].edge, Edge::kNegedge);
}

TEST(ParserA602, AlwaysConstruct_AlwaysLatch) {
  auto r = Parse(
      "module m;\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
}

TEST(ParserA602, AlwaysConstruct_ImplicitSensitivityStar) {
  // @* implicit sensitivity
  auto r = Parse(
      "module m;\n"
      "  always @* y = a + b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
}

TEST(ParserA602, AlwaysConstruct_ImplicitSensitivityParenStar) {
  // @(*) implicit sensitivity
  auto r = Parse(
      "module m;\n"
      "  always @(*) y = a + b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
}

TEST(ParserA602, AlwaysConstruct_WithBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) begin\n"
      "    q <= d;\n"
      "    r <= e;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

// =============================================================================
// A.6.2 Production: always_keyword
// always_keyword ::= always | always_comb | always_latch | always_ff
// =============================================================================

TEST(ParserA602, AlwaysKeyword_AllFourVariants) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) a = 1;\n"
      "  always_comb b = 2;\n"
      "  always_latch if (en) c = 3;\n"
      "  always_ff @(posedge clk) d <= 4;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto blocks =
      FindItems(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_EQ(blocks.size(), 4u);
  EXPECT_EQ(blocks[0]->always_kind, AlwaysKind::kAlways);
  EXPECT_EQ(blocks[1]->always_kind, AlwaysKind::kAlwaysComb);
  EXPECT_EQ(blocks[2]->always_kind, AlwaysKind::kAlwaysLatch);
  EXPECT_EQ(blocks[3]->always_kind, AlwaysKind::kAlwaysFF);
}

// =============================================================================
// A.6.2 Production: final_construct
// final_construct ::= final function_statement
// =============================================================================

TEST(ParserA602, FinalConstruct_SingleStmt) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
}

TEST(ParserA602, FinalConstruct_BeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  final begin\n"
      "    $display(\"test1\");\n"
      "    $display(\"test2\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

TEST(ParserA602, FinalConstruct_Multiple) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"a\");\n"
      "  final $display(\"b\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto finals = FindItems(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock);
  EXPECT_EQ(finals.size(), 2u);
}

// =============================================================================
// A.6.2 Production: blocking_assignment
// blocking_assignment ::=
//   variable_lvalue = delay_or_event_control expression
//   | nonrange_variable_lvalue = dynamic_array_new
//   | [implicit_class_handle . | class_scope | package_scope]
//     hierarchical_variable_identifier select = class_new
//   | operator_assignment
//   | inc_or_dec_expression
// =============================================================================

TEST(ParserA602, BlockingAssignment_Simple) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a = 42; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserA602, BlockingAssignment_WithIntraDelay) {
  // §10.4.1: blocking with intra-assignment delay
  auto r = Parse(
      "module m;\n"
      "  initial begin a = #10 b; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(ParserA602, BlockingAssignment_WithIntraEvent) {
  // §10.4.2: blocking with intra-assignment event
  auto r = Parse(
      "module m;\n"
      "  initial begin a = @(posedge clk) b; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_FALSE(stmt->events.empty());
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(ParserA602, BlockingAssignment_WithRepeatEvent) {
  // §9.4.5: repeat(N) @(event) intra-assignment timing
  auto r = Parse(
      "module m;\n"
      "  initial begin a = repeat(3) @(posedge clk) b; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  EXPECT_FALSE(stmt->events.empty());
}

TEST(ParserA602, BlockingAssignment_ConcatLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin {a, b} = {c, d}; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

TEST(ParserA602, BlockingAssignment_BitSelectLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin mem[3] = 8'hFF; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(ParserA602, BlockingAssignment_PartSelectLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin data[7:0] = 8'hAB; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(ParserA602, BlockingAssignment_DynamicArrayNew) {
  // nonrange_variable_lvalue = dynamic_array_new
  auto r = Parse(
      "module m;\n"
      "  initial begin arr = new[10]; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserA602, BlockingAssignment_DynamicArrayNewWithInit) {
  // dynamic_array_new with copy initializer: new[size](init)
  auto r = Parse(
      "module m;\n"
      "  initial begin arr = new[10](old_arr); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserA602, BlockingAssignment_ClassNew) {
  // class_new: obj = new;
  auto r = Parse(
      "module m;\n"
      "  initial begin obj = new; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserA602, BlockingAssignment_ClassNewWithArgs) {
  // class_new with arguments: obj = new(arg1, arg2)
  auto r = Parse(
      "module m;\n"
      "  initial begin obj = new(1, 2); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserA602, BlockingAssignment_IncExpression) {
  // inc_or_dec_expression: i++
  auto r = Parse(
      "module m;\n"
      "  initial begin i++; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  // i++ parses as expression statement
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kPostfixUnary);
}

TEST(ParserA602, BlockingAssignment_DecExpression) {
  // inc_or_dec_expression: j--
  auto r = Parse(
      "module m;\n"
      "  initial begin j--; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kPostfixUnary);
}

TEST(ParserA602, BlockingAssignment_PrefixInc) {
  // prefix inc: ++i
  auto r = Parse(
      "module m;\n"
      "  initial begin ++i; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kUnary);
}

TEST(ParserA602, BlockingAssignment_PrefixDec) {
  // prefix dec: --j
  auto r = Parse(
      "module m;\n"
      "  initial begin --j; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kUnary);
}

TEST(ParserA602, BlockingAssignment_ParenthesizedIntraDelay) {
  // Parenthesized intra-assignment delay with min:typ:max
  auto r = Parse(
      "module m;\n"
      "  initial begin a = #(1:2:3) b; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
}
