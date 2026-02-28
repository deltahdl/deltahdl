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

// ---------------------------------------------------------------------------
// iff guard on no-edge event at statement level with comparison
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardNoEdgeStmtComparison) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(data iff enable == 1) y = data;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with unary negation in guard expression
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardUnaryNegation) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff !bypass) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  ASSERT_NE(item->sensitivity[0].iff_condition, nullptr);
  EXPECT_EQ(item->sensitivity[0].iff_condition->kind, ExprKind::kUnary);
}

// ---------------------------------------------------------------------------
// iff guard with bitwise-and in guard expression
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardBitwiseAnd) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff (mask & enable)) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// ParseOk: three events all with iff guards (or-separated)
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardThreeEventsOr) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  always @(posedge a iff g1 or negedge b iff g2 or edge c iff g3)\n"
      "    q <= d;\n"
      "endmodule\n"));
}

// ---------------------------------------------------------------------------
// ParseOk: iff guard in always block with nonblocking assignment
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardNonblockingAssign) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @(posedge clk iff valid)\n"
              "    data_out <= data_in;\n"
              "endmodule\n"));
}

// ---------------------------------------------------------------------------
// Verify iff condition absent when not specified
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_NoIffConditionWhenAbsent) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_EQ(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// Verify body is preserved under iff guard at statement level
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardStmtLevelBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(negedge clk iff active) begin\n"
      "      a = 1;\n"
      "      b = 2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
  EXPECT_GE(stmt->body->stmts.size(), 2u);
}

// §3.3 Continuous assignments
TEST(ParserClause03, Cl3_3_ContinuousAssignment) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  logic a, b, y;\n"
      "  assign y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FindItemByKind(r, ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
}

TEST(Lexical, ContAssign_WithDelay) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  wire out, in;\n"
      "  assign #5 out = in;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  const auto* assign_item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kContAssign);
  ASSERT_NE(assign_item, nullptr) << "no continuous assignment found";
  ASSERT_NE(assign_item->assign_delay, nullptr);
  EXPECT_EQ(assign_item->assign_delay->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(assign_item->assign_delay->int_val, 5);
}

TEST(Lexical, ContAssign_WithParenDelay) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  wire out, in;\n"
      "  assign #(10) out = in;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    found = true;
    ASSERT_NE(item->assign_delay, nullptr);
    EXPECT_EQ(item->assign_delay->int_val, 10);
  }
  EXPECT_TRUE(found);
}

TEST(Lexical, ContAssign_NoDelay) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    EXPECT_EQ(item->assign_delay, nullptr);
  }
}

TEST(Parser, ContinuousAssignment) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  logic a, b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found_assign = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      found_assign = true;
    }
  }
  EXPECT_TRUE(found_assign);
}

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

TEST(Lexical, AssignmentPattern_Positional) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  logic [3:0] a;\n"
      "  initial a = '{1, 0, 1, 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, AssignmentPattern_Named) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  initial begin\n"
      "    logic [7:0] x;\n"
      "    x = '{default: 'x};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
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
