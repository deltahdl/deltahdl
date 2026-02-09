#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Stmt* NthInitialStmt(ParseResult& r, size_t n) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      if (n < item->body->stmts.size()) return item->body->stmts[n];
    }
  }
  return nullptr;
}

// =============================================================================
// LRM section 10.6.1 -- Procedural assign / deassign
// =============================================================================

TEST(ParserSection10, ProceduralAssign) {
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "q");
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection10, ProceduralDeassign) {
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    deassign q;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "q");
  EXPECT_EQ(stmt->rhs, nullptr);
}

TEST(ParserSection10, ProceduralAssignThenDeassign) {
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 1;\n"
      "    deassign q;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kAssign);
  EXPECT_EQ(s1->kind, StmtKind::kDeassign);
}

// =============================================================================
// LRM section 10.6.2 -- Force / release
// =============================================================================

TEST(ParserSection10, Force) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    force w = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "w");
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection10, Release) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    release w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "w");
  EXPECT_EQ(stmt->rhs, nullptr);
}

TEST(ParserSection10, ForceThenRelease) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    force w = 1'b1;\n"
      "    release w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kForce);
  EXPECT_EQ(s1->kind, StmtKind::kRelease);
}

// =============================================================================
// LRM section 10.4.1 -- Intra-assignment delay
// =============================================================================

TEST(ParserSection10, BlockingIntraAssignDelay) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    a = #10 b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  ASSERT_NE(stmt->delay, nullptr);
}

TEST(ParserSection10, NonblockingIntraAssignDelay) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    a <= #5 b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  ASSERT_NE(stmt->delay, nullptr);
}

// =============================================================================
// LRM section 10.4.2 -- Intra-assignment event control
// =============================================================================

TEST(ParserSection10, BlockingIntraAssignEvent) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, clk;\n"
      "  initial begin\n"
      "    a = @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

TEST(ParserSection10, NonblockingIntraAssignEvent) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, clk;\n"
      "  initial begin\n"
      "    a <= @(negedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
}

// =============================================================================
// LRM section 10.11 -- Net aliasing
// =============================================================================

TEST(ParserSection10, NetAliasTwoNets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  alias a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  auto* mod = r.cu->modules[0];
  // Find the alias item.
  ModuleItem* alias_item = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kAlias) {
      alias_item = item;
      break;
    }
  }
  ASSERT_NE(alias_item, nullptr);
  ASSERT_EQ(alias_item->alias_nets.size(), 2u);
}

TEST(ParserSection10, NetAliasThreeNets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c;\n"
      "  alias a = b = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* alias_item = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kAlias) {
      alias_item = item;
      break;
    }
  }
  ASSERT_NE(alias_item, nullptr);
  ASSERT_EQ(alias_item->alias_nets.size(), 3u);
}
