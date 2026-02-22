// Tests for A.8.5 — Expression left-side values — Parser

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

static ModuleItem *FirstContAssign(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign)
      return item;
  }
  return nullptr;
}

} // namespace

// =============================================================================
// A.8.5 Expression left-side values — net_lvalue
// =============================================================================

// § net_lvalue — ps_or_hierarchical_net_identifier constant_select (simple net)

TEST(ParserA85, NetLvalueSimpleIdent) {
  auto r = Parse("module m; wire a, b; assign a = b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(ca->assign_lhs->text, "a");
}

// § net_lvalue — ps_or_hierarchical_net_identifier constant_select (bit select)

TEST(ParserA85, NetLvalueConstBitSelect) {
  auto r =
      Parse("module m; wire [7:0] a; wire b; assign a[3] = b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kSelect);
  ASSERT_NE(ca->assign_lhs->base, nullptr);
  EXPECT_EQ(ca->assign_lhs->base->text, "a");
}

// § net_lvalue — ps_or_hierarchical_net_identifier constant_select (part
// select)

TEST(ParserA85, NetLvalueConstPartSelect) {
  auto r = Parse(
      "module m; wire [7:0] a; wire [3:0] b; assign a[7:4] = b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kSelect);
  ASSERT_NE(ca->assign_lhs->index_end, nullptr);
}

// § net_lvalue — { net_lvalue { , net_lvalue } } (concatenation)

TEST(ParserA85, NetLvalueConcatenation) {
  auto r = Parse("module m; wire [7:0] a; wire [3:0] b, c; assign {b, c} = a; "
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(ca->assign_lhs->elements.size(), 2u);
}

// § net_lvalue — nested concatenation

TEST(ParserA85, NetLvalueNestedConcatenation) {
  auto r = Parse("module m; wire a, b, c, d;\n"
                 "  assign {{a, b}, {c, d}} = 4'hF;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(ca->assign_lhs->elements.size(), 2u);
  EXPECT_EQ(ca->assign_lhs->elements[0]->kind, ExprKind::kConcatenation);
}

// § net_lvalue — concatenation with selects

TEST(ParserA85, NetLvalueConcatWithSelects) {
  auto r = Parse("module m; wire [7:0] a; wire [3:0] b;\n"
                 "  assign {a[7:4], b} = 8'hFF;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(ca->assign_lhs->elements[0]->kind, ExprKind::kSelect);
}

// =============================================================================
// A.8.5 Expression left-side values — variable_lvalue
// =============================================================================

// § variable_lvalue — hierarchical_variable_identifier (simple variable)

TEST(ParserA85, VarLvalueSimpleIdent) {
  auto r = Parse("module m; logic x; initial x = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->lhs->text, "x");
}

// § variable_lvalue — hierarchical_variable_identifier select (bit select)

TEST(ParserA85, VarLvalueBitSelect) {
  auto r = Parse("module m; logic [7:0] x; initial x[3] = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->lhs->base, nullptr);
  EXPECT_EQ(stmt->lhs->base->text, "x");
  ASSERT_NE(stmt->lhs->index, nullptr);
  EXPECT_EQ(stmt->lhs->index_end, nullptr);
}

// § variable_lvalue — hierarchical_variable_identifier select (part select)

TEST(ParserA85, VarLvaluePartSelect) {
  auto r = Parse("module m; logic [7:0] x; initial x[7:4] = 4'hF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->lhs->index, nullptr);
  ASSERT_NE(stmt->lhs->index_end, nullptr);
}

// § variable_lvalue — hierarchical_variable_identifier select (indexed part
// select +)

TEST(ParserA85, VarLvalueIndexedPartSelectPlus) {
  auto r =
      Parse("module m; logic [15:0] x; initial x[4+:4] = 4'hF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(stmt->lhs->is_part_select_plus);
}

// § variable_lvalue — hierarchical_variable_identifier select (indexed part
// select -)

TEST(ParserA85, VarLvalueIndexedPartSelectMinus) {
  auto r =
      Parse("module m; logic [15:0] x; initial x[7-:4] = 4'hF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(stmt->lhs->is_part_select_minus);
}

// § variable_lvalue — hierarchical_variable_identifier select (member access)

TEST(ParserA85, VarLvalueMemberAccess) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  initial p.hi = 8'hAB;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

// § variable_lvalue — { variable_lvalue { , variable_lvalue } }
// (concatenation)

TEST(ParserA85, VarLvalueConcatenation) {
  auto r = Parse("module m; logic [3:0] a, b; logic [7:0] c;\n"
                 "  initial {a, b} = c;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements.size(), 2u);
}

// § variable_lvalue — nested concatenation

TEST(ParserA85, VarLvalueNestedConcatenation) {
  auto r = Parse("module m; logic a, b, c, d;\n"
                 "  initial {{a, b}, {c, d}} = 4'hF;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements[0]->kind, ExprKind::kConcatenation);
}

// § variable_lvalue — streaming_concatenation

TEST(ParserA85, VarLvalueStreamingConcat) {
  auto r = Parse("module m; logic [31:0] a, b;\n"
                 "  initial {>> {a}} = b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kStreamingConcat);
}

// § variable_lvalue — streaming_concatenation with slice_size

TEST(ParserA85, VarLvalueStreamingConcatSliceSize) {
  auto r = Parse("module m; logic [31:0] a, b;\n"
                 "  initial {>> 8 {a}} = b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kStreamingConcat);
}

// § variable_lvalue — nonblocking assignment LHS

TEST(ParserA85, VarLvalueNonblocking) {
  auto r = Parse("module m; logic x; initial x <= 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
}

// § variable_lvalue — nonblocking assignment with concatenation LHS

TEST(ParserA85, VarLvalueNonblockingConcat) {
  auto r = Parse("module m; logic [3:0] a, b;\n"
                 "  initial {a, b} <= 8'hFF;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

// § variable_lvalue — compound assignment +=

TEST(ParserA85, VarLvalueCompoundAdd) {
  auto r = Parse("module m; int x; initial x += 5; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
}

// § variable_lvalue — compound assignment with bit select LHS

TEST(ParserA85, VarLvalueCompoundBitSelect) {
  auto r = Parse("module m; logic [7:0] x; initial x[3] |= 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

// § variable_lvalue — pre-increment (++ as lvalue modifier)

TEST(ParserA85, VarLvaluePreIncrement) {
  auto r = Parse("module m; int x; initial ++x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § variable_lvalue — post-increment

TEST(ParserA85, VarLvaluePostIncrement) {
  auto r = Parse("module m; int x; initial x++; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § variable_lvalue — pre-decrement

TEST(ParserA85, VarLvaluePreDecrement) {
  auto r = Parse("module m; int x; initial --x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § variable_lvalue — post-decrement

TEST(ParserA85, VarLvaluePostDecrement) {
  auto r = Parse("module m; int x; initial x--; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § variable_lvalue — multi-dimensional array element select

TEST(ParserA85, VarLvalueMultiDimSelect) {
  auto r = Parse("module m; logic [7:0] mem [0:3][0:3];\n"
                 "  initial mem[1][2] = 8'hAB;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

// § variable_lvalue — force statement LHS

TEST(ParserA85, VarLvalueForce) {
  auto r = Parse("module m; logic x; initial force x = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § variable_lvalue — release statement LHS

TEST(ParserA85, VarLvalueRelease) {
  auto r = Parse("module m; logic x;\n"
                 "  initial begin force x = 1; release x; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.5 Expression left-side values — nonrange_variable_lvalue
// =============================================================================

// § nonrange_variable_lvalue — simple identifier (no range)

TEST(ParserA85, NonrangeVarLvalueSimple) {
  auto r = Parse("module m; int x; initial x = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->lhs->text, "x");
}

// § nonrange_variable_lvalue — member access (no range)

TEST(ParserA85, NonrangeVarLvalueMemberAccess) {
  auto r =
      Parse("module m;\n"
            "  typedef struct packed { logic [7:0] a; logic [7:0] b; } s_t;\n"
            "  s_t s;\n"
            "  initial s.a = 8'h12;\n"
            "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}
