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
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult Parse(const std::string &src) {
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
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static ModuleItem *FindItemByKind(const std::vector<ModuleItem *> &items,
                                  ModuleItemKind kind) {
  for (auto *item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

// =============================================================================
// §16.3 Immediate assertions — assert
// =============================================================================

TEST(ParserSection16, ImmediateAssertBasicKind) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(a == b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_NE(stmt->assert_expr, nullptr);
}

TEST(ParserSection16, ImmediateAssertBasicNoActions) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(a == b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

TEST(ParserSection16, ImmediateAssertWithElseKind) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(x > 0) $display(\"ok\"); else $error(\"fail\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_NE(stmt->assert_expr, nullptr);
}

TEST(ParserSection16, ImmediateAssertWithElseActions) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(x > 0) $display(\"ok\"); else $error(\"fail\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(ParserSection16, ImmediateAssertPassOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(valid) $display(\"passed\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

// =============================================================================
// §16.3 Immediate assertions — assume
// =============================================================================

TEST(ParserSection16, ImmediateAssumeBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assume(x != 0);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_NE(stmt->assert_expr, nullptr);
}

TEST(ParserSection16, ImmediateAssumeWithElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assume(y > 0) $display(\"ok\"); else $error(\"bad\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

// =============================================================================
// §16.3 Immediate assertions — cover
// =============================================================================

TEST(ParserSection16, ImmediateCoverBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    cover(cond);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_NE(stmt->assert_expr, nullptr);
}

TEST(ParserSection16, ImmediateCoverWithPass) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    cover(hit) $display(\"covered\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  // cover does not have else branch
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

// =============================================================================
// §16.4 Deferred immediate assertions (#0)
// =============================================================================

TEST(ParserSection16, DeferredAssertHash0) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert #0 (data_valid);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_NE(stmt->assert_expr, nullptr);
}

// =============================================================================
// §16.5 Concurrent assertions — assert property (module-level)
// =============================================================================

TEST(ParserSection16, AssertPropertyModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  bool found = false;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssertProperty) {
      found = true;
      EXPECT_NE(item->assert_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParserSection16, AssertPropertyWithElse) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack)\n"
      "    $display(\"ok\"); else $error(\"fail\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_pass_stmt, nullptr);
  EXPECT_NE(ap->assert_fail_stmt, nullptr);
}

// =============================================================================
// §16.5 Concurrent — assume property
// =============================================================================

TEST(ParserSection16, AssumePropertyModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) valid);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssumeProperty) {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// =============================================================================
// §16.5 Concurrent — cover property
// =============================================================================

TEST(ParserSection16, CoverPropertyModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a && b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kCoverProperty) {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// =============================================================================
// §16.12 Property declarations
// =============================================================================

TEST(ParserSection16, PropertyDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  property p_req_ack;\n"
      "    @(posedge clk) req |-> ack;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl) {
      found = true;
      EXPECT_EQ(item->name, "p_req_ack");
    }
  }
  EXPECT_TRUE(found);
}

// =============================================================================
// §16.8 Sequence declarations
// =============================================================================

TEST(ParserSection16, SequenceDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_req;\n"
      "    req ##1 ack;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl) {
      found = true;
      EXPECT_EQ(item->name, "s_req");
    }
  }
  EXPECT_TRUE(found);
}

// =============================================================================
// Combination: property used with assert
// =============================================================================

TEST(ParserSection16, PropertyDeclAndAssertProperty) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  assert property (p1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found_prop = false;
  bool found_assert = false;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl) found_prop = true;
    if (item->kind == ModuleItemKind::kAssertProperty) found_assert = true;
  }
  EXPECT_TRUE(found_prop);
  EXPECT_TRUE(found_assert);
}

// --- Deferred immediate assertions at module level (§16.4) ---

TEST(ParserSection16, DeferredAssertModuleLevel) {
  auto r = Parse(
      "module top();\n"
      "  logic a = 1;\n"
      "  assert #0 (a != 0);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection16, DeferredAssumeModuleLevel) {
  auto r = Parse(
      "module top();\n"
      "  logic a = 1;\n"
      "  assume #0 (a != 0);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection16, DeferredCoverModuleLevel) {
  auto r = Parse(
      "module top();\n"
      "  logic a = 1;\n"
      "  cover #0 (a != 0);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection16, AssertFinalModuleLevel) {
  auto r = Parse(
      "module top();\n"
      "  logic a = 1;\n"
      "  assert final (a != 0);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection16, ExpectStatement) {
  auto r = Parse(
      "module top();\n"
      "  logic clk, a, b;\n"
      "  initial begin\n"
      "    expect (@(posedge clk) a ##1 b);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

// =============================================================================
// §16.2 Immediate assertions — overview (assert, assume, cover in one module)
// =============================================================================

TEST(ParserSection16, OverviewAllThreeImmediateKinds) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(a);\n"
      "    assume(b);\n"
      "    cover(c);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, OverviewAssertWithComplexExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(a inside {1, 2, 3});\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.4 Deferred assertions — additional forms
// =============================================================================

TEST(ParserSection16, DeferredAssumeHash0WithAction) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assume #0 (valid) $display(\"assumed\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.4.1 Deferred assertion reporting
// =============================================================================

TEST(ParserSection16, DeferredAssertHash0PassAndFail) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert #0 (data_ok)\n"
      "      $display(\"pass\"); else $error(\"fail\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

// =============================================================================
// §16.5 Concurrent assertions overview — clocked property
// =============================================================================

TEST(ParserSection16, ConcurrentAssertWithClock) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

TEST(ParserSection16, ConcurrentAssertNegedgeClock) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(negedge clk) a |-> b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.5.1 Concurrent assert/assume/cover
// =============================================================================

TEST(ParserSection16, ConcurrentAssumePropertyWithAction) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |-> gnt)\n"
      "    else $error(\"assumption failed\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_fail_stmt, nullptr);
}

TEST(ParserSection16, ConcurrentCoverPropertyWithStmt) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b)\n"
      "    $display(\"covered\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *cp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(cp, nullptr);
}

// =============================================================================
// §16.7 Sequences — concatenation and delay
// =============================================================================

TEST(ParserSection16, SequenceConcatDelay1) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req ##1 gnt ##1 !req);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceConcatDelay2) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req ##2 gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceDelayRange) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req ##[4:32] gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.9 Sequence operations — repetition
// =============================================================================

TEST(ParserSection16, SequenceConsecutiveRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a[*3] |-> b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceRepetitionRange) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a[*1:3] ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceGotoRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack[->1]);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.9.4 Sequence throughout
// =============================================================================

TEST(ParserSection16, SequenceThroughoutBasic) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) !burst_mode throughout (##2 trdy[*7]));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceThroughoutInSeqDecl) {
  auto r = Parse(
      "module m;\n"
      "  sequence burst_rule;\n"
      "    @(posedge clk)\n"
      "    (!burst_mode) throughout (##2 (trdy && irdy)[*7]);\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *sq =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(sq, nullptr);
}

// =============================================================================
// §16.9.11 Sequence methods — triggered
// =============================================================================

TEST(ParserSection16, SequenceTriggeredMethod) {
  auto r = Parse(
      "module m;\n"
      "  sequence e1;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  sequence rule;\n"
      "    @(posedge clk) reset ##1 inst ##1 e1.triggered ##1 done;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceMatchedMethod) {
  auto r = Parse(
      "module m;\n"
      "  sequence e1;\n"
      "    @(posedge clk1) a ##1 b;\n"
      "  endsequence\n"
      "  sequence e2;\n"
      "    @(posedge clk2) reset ##1 e1.matched ##1 done;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.12 Property declarations — with formal arguments
// =============================================================================

TEST(ParserSection16, PropertyDeclWithFormals) {
  auto r = Parse(
      "module m;\n"
      "  property p_req_ack(req, ack);\n"
      "    @(posedge clk) req |-> ##[1:3] ack;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *pd =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->name, "p_req_ack");
}

TEST(ParserSection16, PropertyDeclWithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty : p1\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.12.7 Property instances / implication
// =============================================================================

TEST(ParserSection16, PropertyOverlappedImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyNonOverlappedImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |=> gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyInstanceWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  property p1(a, b);\n"
      "    a |-> ##1 b;\n"
      "  endproperty\n"
      "  assert property (@(posedge clk) p1(req, ack));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.13.6 Disable iff
// =============================================================================

TEST(ParserSection16, DisableIffInAssertProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) disable iff (rst) a |-> b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, DisableIffInPropertyDecl) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    disable iff (rst == 2)\n"
      "    @(posedge clk) not (a ##1 b);\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, DisableIffWithComplexExpr) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) disable iff (rst || !en)\n"
      "    req |-> ##[1:5] ack);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.14 Concurrent assertions — procedural context
// =============================================================================

// =============================================================================
// §16.14.2 Sequence property — strong/weak
// =============================================================================

TEST(ParserSection16, StrongSequenceProperty) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) strong(a ##1 b ##1 c));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, WeakSequenceProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) weak(a ##1 b));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.14.6 Property case
// =============================================================================

TEST(ParserSection16, PropertyCaseBasic) {
  auto r = Parse(
      "module m;\n"
      "  property p_delay(logic [1:0] delay);\n"
      "    case (delay)\n"
      "      2'd0 : a && b;\n"
      "      2'd1 : a ##2 b;\n"
      "      2'd2 : a ##4 b;\n"
      "      default: 0;\n"
      "    endcase\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyCaseInAssert) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    @(posedge clk)\n"
      "    case (mode)\n"
      "      2'b00 : a |-> b;\n"
      "      2'b01 : a |-> ##1 b;\n"
      "      2'b10 : a |-> ##2 b;\n"
      "    endcase\n"
      "  endproperty\n"
      "  assert property (p1);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.14.6.2 Property if-else
// =============================================================================

TEST(ParserSection16, PropertyIfElse) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk)\n"
      "    if (mode) a |-> b\n"
      "    else a |-> c);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyIfWithoutElse) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk)\n"
      "    if (en) a |-> ##[1:3] b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyIfElseInDecl) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    @(posedge clk)\n"
      "    if (sel)\n"
      "      req |-> ##1 ack\n"
      "    else\n"
      "      req |-> ##2 ack;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.14.7 Property negation
// =============================================================================

TEST(ParserSection16, PropertyNegation) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) not (a ##1 b));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyNegationStrong) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) not strong(a ##1 b));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.14.8 Property disjunction and conjunction
// =============================================================================

TEST(ParserSection16, PropertyDisjunction) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a |-> b) or (c |-> d));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyConjunction) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a |-> b) and (c |-> d));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyDisjunctionAndConjunctionCombined) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk)\n"
      "    ((a |-> b) and (c |-> d)) or (e |-> f));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}
