// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

static ModuleItem* FindItemByKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
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

namespace {

// ===========================================================================
// §10.9-10.10: Assignment pattern evaluation
// ===========================================================================
TEST(Lexical, AssignmentPattern_DefaultZero) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  logic [7:0] a;\n"
      "  initial a = '{default: 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // Should parse without error.
  ASSERT_EQ(r.cu->modules.size(), 1);
}

// net_alias: alias net1 = net2 = net3;
TEST(SourceText, NetAlias) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b, c;\n"
      "  alias a = b = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  // 3 wire decls + 1 alias
  auto* alias_item = items.back();
  EXPECT_EQ(alias_item->kind, ModuleItemKind::kAlias);
  EXPECT_EQ(alias_item->alias_nets.size(), 3u);
}

// =============================================================================
// LRM section 10.6.1 -- Procedural assign / deassign
// =============================================================================
TEST(ParserSection10, ProceduralAssignKind) {
  auto r = ParseWithPreprocessor(
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
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection10, ProceduralAssignLhs) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "q");
}

TEST(ParserSection10, ProceduralDeassignKind) {
  auto r = ParseWithPreprocessor(
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
  EXPECT_EQ(stmt->rhs, nullptr);
}

TEST(ParserSection10, ProceduralDeassignLhs) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    deassign q;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "q");
}

TEST(ParserSection10, ProceduralAssignThenDeassign) {
  auto r = ParseWithPreprocessor(
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
TEST(ParserSection10, ForceKind) {
  auto r = ParseWithPreprocessor(
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
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection10, ForceLhs) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    force w = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "w");
}

TEST(ParserSection10, ReleaseKind) {
  auto r = ParseWithPreprocessor(
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
  EXPECT_EQ(stmt->rhs, nullptr);
}

TEST(ParserSection10, ReleaseLhs) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    release w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "w");
}

TEST(ParserSection10, ForceThenRelease) {
  auto r = ParseWithPreprocessor(
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
TEST(ParserSection10, BlockingIntraAssignDelayKind) {
  auto r = ParseWithPreprocessor(
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
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(ParserSection10, BlockingIntraAssignDelayOperands) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    a = #10 b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection10, NonblockingIntraAssignDelayKind) {
  auto r = ParseWithPreprocessor(
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
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(ParserSection10, NonblockingIntraAssignDelayOperands) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    a <= #5 b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

// =============================================================================
// LRM section 10.4.2 -- Intra-assignment event control
// =============================================================================
TEST(ParserSection10, BlockingIntraAssignEventKind) {
  auto r = ParseWithPreprocessor(
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
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection10, BlockingIntraAssignEventEdge) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg a, b, clk;\n"
      "  initial begin\n"
      "    a = @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

TEST(ParserSection10, NonblockingIntraAssignEventKind) {
  auto r = ParseWithPreprocessor(
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
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection10, NonblockingIntraAssignEventEdge) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg a, b, clk;\n"
      "  initial begin\n"
      "    a <= @(negedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
}

// =============================================================================
// LRM section 10.11 -- Net aliasing
// =============================================================================
TEST(ParserSection10, NetAliasTwoNets) {
  auto r = ParseWithPreprocessor(
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
  auto r = ParseWithPreprocessor(
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

TEST(ParserSection10, ContinuousAssignBasic) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  auto* ca = FindItemByKind(mod->items, ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  ASSERT_NE(ca->assign_rhs, nullptr);
}

TEST(ParserSection10, NetDeclAssignment) {
  auto r = ParseWithPreprocessor(
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
  auto r = ParseWithPreprocessor(
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
  auto r = ParseWithPreprocessor(
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
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  logic [7:0] data = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  EXPECT_NE(mod->items[0]->init_expr, nullptr);
}

// =============================================================================
// LRM section 10.8 -- Operator assignments (+=, -=, etc.)
// =============================================================================
TEST(ParserSection10, OperatorAssignPlusEq) {
  auto r = ParseWithPreprocessor(
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
  auto r = ParseWithPreprocessor(
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
  auto r = ParseWithPreprocessor(
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

}  // namespace
