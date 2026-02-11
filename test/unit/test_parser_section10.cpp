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

// =============================================================================
// LRM section 10.3.1/10.3.2 -- Continuous assignment
// =============================================================================

TEST(ParserSection10, ContinuousAssignBasic) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  bool found = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      found = true;
      ASSERT_NE(item->assign_lhs, nullptr);
      ASSERT_NE(item->assign_rhs, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParserSection10, NetDeclAssignment) {
  auto r = Parse(
      "module m;\n"
      "  wire a = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  auto* item = mod->items[0];
  EXPECT_EQ(item->name, "a");
  EXPECT_NE(item->init_expr, nullptr);
}

// =============================================================================
// LRM section 10.3.3 -- Continuous assignment delays
// =============================================================================

TEST(ParserSection10, ContinuousAssignDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #10 a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      EXPECT_NE(item->assign_delay, nullptr);
    }
  }
}

// =============================================================================
// LRM section 10.5 -- Variable declaration assignment
// =============================================================================

TEST(ParserSection10, VarDeclAssignment) {
  auto r = Parse(
      "module m;\n"
      "  int x = 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  auto* item = mod->items[0];
  EXPECT_EQ(item->name, "x");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection10, VarDeclAssignmentLogic) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] data = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  EXPECT_NE(mod->items[0]->init_expr, nullptr);
}

// =============================================================================
// LRM section 10.4 -- Blocking and nonblocking assignments
// =============================================================================

TEST(ParserSection10, BlockingAssignSimple) {
  auto r = Parse(
      "module m;\n"
      "  initial a = 1;\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection10, NonblockingAssignSimple) {
  auto r = Parse(
      "module m;\n"
      "  initial a <= 1;\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
}

// =============================================================================
// LRM section 10.8 -- Operator assignments (+=, -=, etc.)
// =============================================================================

TEST(ParserSection10, OperatorAssignPlusEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a += 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection10, OperatorAssignMinusEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a -= 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection10, OperatorAssignStarEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a *= 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection10, OperatorAssignSlashEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a /= 4;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection10, OperatorAssignPercentEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a %= 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection10, OperatorAssignAmpEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a &= 8'hFF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection10, OperatorAssignPipeEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a |= 8'h01;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection10, OperatorAssignCaretEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a ^= 8'hAA;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection10, OperatorAssignLtLtEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <<= 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection10, OperatorAssignGtGtEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a >>= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection10, OperatorAssignLtLtLtEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <<<= 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection10, OperatorAssignGtGtGtEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a >>>= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

// =============================================================================
// LRM section 10.3.4 -- Continuous assignment with drive strengths
// =============================================================================

TEST(ParserSection10, ContinuousAssignMultipleTargets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  assign a = b, c = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  int count = 0;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kContAssign) count++;
  }
  EXPECT_GE(count, 1);
}

// §10.3.4: Drive strength on continuous assignment.
TEST(ParserSection10, ContinuousAssignDriveStrength) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, weak1) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* ca = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      ca = item;
      break;
    }
  }
  ASSERT_NE(ca, nullptr);
  // 4=strong, 2=weak (parser encoding:
  // 0=none,1=highz,2=weak,3=pull,4=strong,5=supply)
  EXPECT_EQ(ca->drive_strength0, 4u);
  EXPECT_EQ(ca->drive_strength1, 2u);
}

// §10.3.4: Drive strength order can be reversed.
TEST(ParserSection10, ContinuousAssignDriveStrengthReversed) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (pull1, supply0) w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* ca = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      ca = item;
      break;
    }
  }
  ASSERT_NE(ca, nullptr);
  EXPECT_EQ(ca->drive_strength0, 5u);  // supply0
  EXPECT_EQ(ca->drive_strength1, 3u);  // pull1
}
