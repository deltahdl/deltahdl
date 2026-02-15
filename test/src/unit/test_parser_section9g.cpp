#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult9g {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9g Parse(const std::string& src) {
  ParseResult9g result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem* FirstAlwaysComb(ParseResult9g& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock) return item;
  }
  return nullptr;
}

static ModuleItem* NthAlwaysComb(ParseResult9g& r, size_t n) {
  size_t count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock) {
      if (count == n) return item;
      ++count;
    }
  }
  return nullptr;
}

static Stmt* FirstAlwaysCombStmt(ParseResult9g& r) {
  auto* item = FirstAlwaysComb(r);
  if (!item || !item->body) return nullptr;
  if (item->body->kind == StmtKind::kBlock) {
    return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
  }
  return item->body;
}

// =============================================================================
// LRM section 9.2.2 -- Always_comb procedure
//
// The always_comb procedure is a combinational logic process with an
// implicit sensitivity list. It executes once at time zero and then
// re-executes whenever any of its input signals change. No explicit
// sensitivity list is permitted.
// =============================================================================

// ---------------------------------------------------------------------------
// 1. Simple blocking assignment in always_comb
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_SimpleBlockingAssign) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c;\n"
      "  always_comb a = b & c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
}

// ---------------------------------------------------------------------------
// 2. always_comb with begin-end block containing multiple assignments
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_BeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, x, y;\n"
      "  always_comb begin\n"
      "    x = a & b;\n"
      "    y = a | b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_EQ(item->body->stmts.size(), 2u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[1]->kind, StmtKind::kBlockingAssign);
}

// ---------------------------------------------------------------------------
// 3. always_comb with if-else statement
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_IfElse) {
  auto r = Parse(
      "module m;\n"
      "  logic sel, a, b, y;\n"
      "  always_comb begin\n"
      "    if (sel)\n"
      "      y = a;\n"
      "    else\n"
      "      y = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
}

// ---------------------------------------------------------------------------
// 4. always_comb with case statement
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_CaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb begin\n"
      "    case (sel)\n"
      "      2'b00: y = 4'h0;\n"
      "      2'b01: y = 4'h1;\n"
      "      2'b10: y = 4'h2;\n"
      "      default: y = 4'hF;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCase);
  ASSERT_EQ(stmt->case_items.size(), 4u);
  EXPECT_TRUE(stmt->case_items[3].is_default);
}

// ---------------------------------------------------------------------------
// 5. always_comb with casex statement
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_CasexStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] opcode;\n"
      "  logic [7:0] result;\n"
      "  always_comb begin\n"
      "    casex (opcode)\n"
      "      4'b1xxx: result = 8'hFF;\n"
      "      4'b01xx: result = 8'h0F;\n"
      "      default: result = 8'h00;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
  ASSERT_EQ(stmt->case_items.size(), 3u);
}

// ---------------------------------------------------------------------------
// 6. always_comb with casez statement
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_CasezStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] req;\n"
      "  logic [1:0] grant;\n"
      "  always_comb begin\n"
      "    casez (req)\n"
      "      4'b???1: grant = 2'b00;\n"
      "      4'b??10: grant = 2'b01;\n"
      "      4'b?100: grant = 2'b10;\n"
      "      4'b1000: grant = 2'b11;\n"
      "      default: grant = 2'b00;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
  ASSERT_EQ(stmt->case_items.size(), 5u);
}

// ---------------------------------------------------------------------------
// 7. always_comb with nested if-else and case
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_NestedIfElseAndCase) {
  auto r = Parse(
      "module m;\n"
      "  logic mode;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] out;\n"
      "  always_comb begin\n"
      "    if (mode) begin\n"
      "      case (sel)\n"
      "        2'd0: out = 8'd10;\n"
      "        2'd1: out = 8'd20;\n"
      "        default: out = 8'd0;\n"
      "      endcase\n"
      "    end else begin\n"
      "      out = 8'd0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
  // The then branch should be a block containing a case statement
  ASSERT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
  ASSERT_GE(stmt->then_branch->stmts.size(), 1u);
  EXPECT_EQ(stmt->then_branch->stmts[0]->kind, StmtKind::kCase);
}

// ---------------------------------------------------------------------------
// 8. always_comb with for loop
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_ForLoop) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] data_in [0:3];\n"
      "  logic [7:0] data_out [0:3];\n"
      "  always_comb begin\n"
      "    for (int i = 0; i < 4; i++)\n"
      "      data_out[i] = data_in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_cond, nullptr);
  EXPECT_NE(stmt->for_body, nullptr);
}

// ---------------------------------------------------------------------------
// 9. always_comb with while loop
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_WhileLoop) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] val;\n"
      "  logic [3:0] count;\n"
      "  always_comb begin\n"
      "    count = 0;\n"
      "    while (val[count] && count < 8)\n"
      "      count = count + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 2u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[1]->kind, StmtKind::kWhile);
}

// ---------------------------------------------------------------------------
// 10. always_comb with foreach loop
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_ForeachLoop) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] arr [0:3];\n"
      "  logic [7:0] inv [0:3];\n"
      "  always_comb begin\n"
      "    foreach (arr[i])\n"
      "      inv[i] = ~arr[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  ASSERT_FALSE(stmt->foreach_vars.empty());
}

// ---------------------------------------------------------------------------
// 11. always_comb with function call
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_FunctionCall) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a, b, result;\n"
      "  function logic [7:0] add(input logic [7:0] x, y);\n"
      "    return x + y;\n"
      "  endfunction\n"
      "  always_comb result = add(a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kCall);
}

// ---------------------------------------------------------------------------
// 12. always_comb with ternary expression
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_TernaryExpression) {
  auto r = Parse(
      "module m;\n"
      "  logic sel, a, b, y;\n"
      "  always_comb y = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kTernary);
}

// ---------------------------------------------------------------------------
// 13. always_comb with concatenation
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_Concatenation) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] c;\n"
      "  always_comb c = {a, b};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(item->body->rhs->elements.size(), 2u);
}

// ---------------------------------------------------------------------------
// 14. always_comb with replication
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_Replication) {
  auto r = Parse(
      "module m;\n"
      "  logic sign_bit;\n"
      "  logic [7:0] extended;\n"
      "  always_comb extended = {8{sign_bit}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kReplicate);
  EXPECT_NE(item->body->rhs->repeat_count, nullptr);
}

// ---------------------------------------------------------------------------
// 15. always_comb with multiple variable assignments
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_MultipleAssignments) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, x, y, z;\n"
      "  always_comb begin\n"
      "    x = a & b;\n"
      "    y = a | c;\n"
      "    z = b ^ c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_EQ(item->body->stmts.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(item->body->stmts[i]->kind, StmtKind::kBlockingAssign);
  }
}

// ---------------------------------------------------------------------------
// 16. always_comb with bit select on LHS
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_BitSelectLHS) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  logic val;\n"
      "  always_comb data[3] = val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->lhs, nullptr);
  EXPECT_EQ(item->body->lhs->kind, ExprKind::kSelect);
}

// ---------------------------------------------------------------------------
// 17. always_comb with part select on LHS
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_PartSelectLHS) {
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] bus;\n"
      "  logic [7:0] low_byte;\n"
      "  always_comb bus[7:0] = low_byte;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->lhs, nullptr);
  EXPECT_EQ(item->body->lhs->kind, ExprKind::kSelect);
  EXPECT_NE(item->body->lhs->index, nullptr);
  EXPECT_NE(item->body->lhs->index_end, nullptr);
}

// ---------------------------------------------------------------------------
// 18. always_comb with struct member access
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_StructMemberAccess) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] addr;\n"
      "    logic [7:0] data;\n"
      "  } pkt_t;\n"
      "  pkt_t pkt;\n"
      "  logic [7:0] a, d;\n"
      "  always_comb begin\n"
      "    pkt.addr = a;\n"
      "    pkt.data = d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 2u);
  // LHS of first assignment should be a member access expression
  EXPECT_EQ(item->body->stmts[0]->lhs->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(item->body->stmts[1]->lhs->kind, ExprKind::kMemberAccess);
}

// ---------------------------------------------------------------------------
// 19. always_comb with unique case
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_UniqueCase) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb begin\n"
      "    unique case (sel)\n"
      "      2'b00: y = 4'd0;\n"
      "      2'b01: y = 4'd1;\n"
      "      2'b10: y = 4'd2;\n"
      "      2'b11: y = 4'd3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
  ASSERT_EQ(stmt->case_items.size(), 4u);
}

// ---------------------------------------------------------------------------
// 20. always_comb with priority case
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_PriorityCase) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] req;\n"
      "  logic [1:0] grant;\n"
      "  always_comb begin\n"
      "    priority case (1'b1)\n"
      "      req[0]: grant = 2'd0;\n"
      "      req[1]: grant = 2'd1;\n"
      "      req[2]: grant = 2'd2;\n"
      "      req[3]: grant = 2'd3;\n"
      "      default: grant = 2'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
  ASSERT_EQ(stmt->case_items.size(), 5u);
}

// ---------------------------------------------------------------------------
// 21. always_comb with local variable declaration
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_LocalVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a, b, result;\n"
      "  always_comb begin\n"
      "    logic [8:0] temp;\n"
      "    temp = a + b;\n"
      "    result = temp[7:0];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 3u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->body->stmts[0]->var_name, "temp");
  EXPECT_EQ(item->body->stmts[1]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[2]->kind, StmtKind::kBlockingAssign);
}

// ---------------------------------------------------------------------------
// 22. always_comb has implicit sensitivity (no sensitivity list on item)
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_ImplicitSensitivity) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c;\n"
      "  always_comb c = a ^ b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
  // always_comb must not have an explicit sensitivity list
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
}

// ---------------------------------------------------------------------------
// 23. always_comb with complex combinational logic (priority encoder)
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_PriorityEncoderPattern) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] req;\n"
      "  logic [1:0] enc;\n"
      "  logic valid;\n"
      "  always_comb begin\n"
      "    enc = 2'b00;\n"
      "    valid = 1'b0;\n"
      "    if (req[3]) begin\n"
      "      enc = 2'b11;\n"
      "      valid = 1'b1;\n"
      "    end else if (req[2]) begin\n"
      "      enc = 2'b10;\n"
      "      valid = 1'b1;\n"
      "    end else if (req[1]) begin\n"
      "      enc = 2'b01;\n"
      "      valid = 1'b1;\n"
      "    end else if (req[0]) begin\n"
      "      enc = 2'b00;\n"
      "      valid = 1'b1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  // Two default assignments plus an if-else-if chain
  ASSERT_GE(item->body->stmts.size(), 3u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[1]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[2]->kind, StmtKind::kIf);
}

// ---------------------------------------------------------------------------
// 24. Multiple always_comb blocks in the same module
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_MultipleAlwaysCombBlocks) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, x, y;\n"
      "  always_comb x = a & b;\n"
      "  always_comb y = a | b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* first = NthAlwaysComb(r, 0);
  auto* second = NthAlwaysComb(r, 1);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first->kind, ModuleItemKind::kAlwaysCombBlock);
  EXPECT_EQ(second->kind, ModuleItemKind::kAlwaysCombBlock);
  ASSERT_NE(first->body, nullptr);
  ASSERT_NE(second->body, nullptr);
}

// ---------------------------------------------------------------------------
// 25. always_comb with array indexing
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_ArrayIndexing) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] mem [0:15];\n"
      "  logic [3:0] addr;\n"
      "  logic [7:0] data;\n"
      "  always_comb data = mem[addr];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kSelect);
}

// ---------------------------------------------------------------------------
// 26. always_comb with unique0 case
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_Unique0Case) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb begin\n"
      "    unique0 case (sel)\n"
      "      2'b00: y = 4'd0;\n"
      "      2'b01: y = 4'd1;\n"
      "      2'b10: y = 4'd2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
  ASSERT_EQ(stmt->case_items.size(), 3u);
}

// ---------------------------------------------------------------------------
// 27. always_comb with concatenation on LHS
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_ConcatenationLHS) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] hi, lo;\n"
      "  logic [7:0] data;\n"
      "  always_comb {hi, lo} = data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->lhs, nullptr);
  EXPECT_EQ(item->body->lhs->kind, ExprKind::kConcatenation);
}

// ---------------------------------------------------------------------------
// 28. always_comb with nested ternary expressions
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_NestedTernary) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic a, b, c, y;\n"
      "  always_comb y = sel[1] ? (sel[0] ? a : b) : c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kTernary);
}

// ---------------------------------------------------------------------------
// 29. always_comb with unique if
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_UniqueIf) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] out;\n"
      "  always_comb begin\n"
      "    unique if (sel == 2'b00)\n"
      "      out = 4'd0;\n"
      "    else if (sel == 2'b01)\n"
      "      out = 4'd1;\n"
      "    else if (sel == 2'b10)\n"
      "      out = 4'd2;\n"
      "    else\n"
      "      out = 4'd3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
}

// ---------------------------------------------------------------------------
// 30. always_comb ParseOk smoke test for full mux with for loop and array
// ---------------------------------------------------------------------------

TEST(ParserSection9, Sec9_2_2_ParseOkComplexMuxPattern) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [3:0] sel;\n"
              "  logic [7:0] inputs [0:15];\n"
              "  logic [7:0] out;\n"
              "  always_comb begin\n"
              "    out = 8'd0;\n"
              "    for (int i = 0; i < 16; i++) begin\n"
              "      if (sel == i[3:0])\n"
              "        out = inputs[i];\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}
