#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

Stmt* FirstInitialStmt(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

}  // namespace

// =============================================================================
// Annex D -- Optional system tasks and system functions
// =============================================================================

// --- D.1: $getpattern ---
TEST(ParserAnnexD2, AnnexDGetpatternParse) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $getpattern(mem_addr);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserAnnexD2, AnnexDGetpatternRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $getpattern(mem_addr);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
}

// --- D.2: $incsave ---
TEST(ParserAnnexD2, AnnexDIncsaveParse) {
  auto r = Parse(
      "module m;\n"
      "  initial $incsave(\"incremental.sav\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserAnnexD2, AnnexDIncsaveExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial $incsave(\"incremental.sav\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

// --- D.3: $input ---
TEST(ParserAnnexD2, AnnexDInput) {
  auto r = Parse(
      "module m;\n"
      "  initial $input(\"commands.txt\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

// --- D.4: $key and $nokey ---
TEST(ParserAnnexD2, AnnexDKeyNokey) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $key(\"keylog.txt\");\n"
      "    $nokey;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// --- D.5: $reset, $reset_count, $reset_value ---
TEST(ParserAnnexD2, AnnexDResetFamily) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $reset;\n"
      "    x = $reset_count;\n"
      "    y = $reset_value;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// --- D.6: $scale ---
TEST(ParserAnnexD2, AnnexDScaleParse) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $scale(hier_ref);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserAnnexD2, AnnexDScaleRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $scale(hier_ref);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
}

// --- D.7: $showscopes with argument ---
TEST(ParserAnnexD2, AnnexDShowscopesArg) {
  auto r = Parse(
      "module m;\n"
      "  initial $showscopes(1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

// --- D.8: $countones as expression ---
TEST(ParserAnnexD2, AnnexDCountonesParse) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $countones(data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserAnnexD2, AnnexDCountonesRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $countones(data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
}

// --- D.9: $isunknown ---
TEST(ParserAnnexD2, AnnexDIsunknownParse) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $isunknown(data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserAnnexD2, AnnexDIsunknownRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $isunknown(data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
}

// --- D.10: $onehot and $onehot0 ---
TEST(ParserAnnexD2, AnnexDOnehot) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = $onehot(state);\n"
      "    y = $onehot0(state);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// =============================================================================
// Annex E -- Optional compiler directives
// =============================================================================

// --- E.1: `default_trireg_strength ---
TEST(ParserAnnexE2, AnnexEDefaultTriregStrength) {
  auto r = Parse(
      "`default_trireg_strength 50\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

// --- E.2: `delay_mode_distributed ---
TEST(ParserAnnexE2, AnnexEDelayModeDistributed) {
  auto r = Parse(
      "`delay_mode_distributed\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

// --- E.3: `delay_mode_path ---
TEST(ParserAnnexE2, AnnexEDelayModePath) {
  auto r = Parse(
      "`delay_mode_path\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

// --- E.4: `delay_mode_unit ---
TEST(ParserAnnexE2, AnnexEDelayModeUnit) {
  auto r = Parse(
      "`delay_mode_unit\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

// --- E.5: All Annex E directives combined ---
TEST(ParserAnnexE2, AnnexEAllDirectivesCombined) {
  auto r = Parse(
      "`default_decay_time 10\n"
      "`default_trireg_strength 100\n"
      "`delay_mode_distributed\n"
      "`delay_mode_path\n"
      "`delay_mode_unit\n"
      "`delay_mode_zero\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

// =============================================================================
// Annex F -- Formal semantics of concurrent assertions
// =============================================================================

TEST(ParserAnnexF, AnnexFAssertPropertySimple) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssertProperty) {
      found = true;
      EXPECT_NE(item->assert_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParserAnnexF, AnnexFAssumeProperty) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |-> ##[1:3] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssumeProperty) {
      found = true;
      EXPECT_NE(item->assert_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParserAnnexF, AnnexFCoverProperty) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kCoverProperty) {
      found = true;
      EXPECT_NE(item->assert_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParserAnnexF, AnnexFPropertyDecl) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    @(posedge clk) a |-> ##1 b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl) {
      found = true;
      EXPECT_EQ(item->name, "p1");
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParserAnnexF, AnnexFSequenceDecl) {
  auto r = Parse(
      "module m;\n"
      "  sequence s1;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl) {
      found = true;
      EXPECT_EQ(item->name, "s1");
    }
  }
  EXPECT_TRUE(found);
}

// --- F.1: Sequence concatenation with ## delay ---
TEST(ParserAnnexF, AnnexFSequenceConcatDelay) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a ##2 b ##3 c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// --- F.2: Sequence repetition [*N] ---
TEST(ParserAnnexF, AnnexFConsecutiveRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a[*3] |-> b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// --- F.3: Goto repetition [->N] ---
TEST(ParserAnnexF, AnnexFGotoRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack[->1]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// --- F.4: Non-consecutive repetition [=N] ---
TEST(ParserAnnexF, AnnexFNonconsecutiveRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack[=2]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// --- F.5: Ranged repetition [*min:max] ---
TEST(ParserAnnexF, AnnexFRangedRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a ##[1:5] b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// --- F.6: first_match ---
TEST(ParserAnnexF, AnnexFFirstMatch) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) first_match(a ##[1:4] b));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// --- F.7: throughout ---
TEST(ParserAnnexF, AnnexFThroughout) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) enable throughout (a ##1 b ##1 c));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// --- F.8: within ---
TEST(ParserAnnexF, AnnexFWithin) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a ##[1:3] b) within (c ##[1:5] d));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// --- F.9: intersect ---
TEST(ParserAnnexF, AnnexFIntersect) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a ##[1:5] b) intersect (c ##[2:4] d));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// --- F.10: Property not ---
TEST(ParserAnnexF, AnnexFPropertyNot) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) not (a |-> b));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// --- F.11: Property and ---
TEST(ParserAnnexF, AnnexFPropertyAnd) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a |-> b) and (c |-> d));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// --- F.12: Property or ---
TEST(ParserAnnexF, AnnexFPropertyOr) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a |-> b) or (c |-> d));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// --- F.13: Overlapping implication |-> ---
TEST(ParserAnnexF, AnnexFOverlapImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a && b |-> c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// --- F.14: Non-overlapping implication |=> ---
TEST(ParserAnnexF, AnnexFNonoverlapImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |=> gnt);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// --- F.15: Property if-else ---
TEST(ParserAnnexF, AnnexFPropertyIfElse) {
  auto r = Parse(
      "module m;\n"
      "  property p_cond;\n"
      "    @(posedge clk) if (mode) a |-> b; else c |-> d;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kPropertyDecl));
}

// --- F.16: Negedge clocking ---
TEST(ParserAnnexF, AnnexFNegedgeClocking) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(negedge clk) a |-> ##1 b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// --- F.17: Sequence with chained concatenation ---
TEST(ParserAnnexF, AnnexFChainedConcat) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_chain;\n"
      "    @(posedge clk) a ##1 b ##1 c ##1 d ##1 e;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kSequenceDecl));
}

// --- F.18: Property with named property reference ---
TEST(ParserAnnexF, AnnexFPropertyReference) {
  auto r = Parse(
      "module m;\n"
      "  property p_base;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  assert property (p_base);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kPropertyDecl));
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// --- F.19: Assert with action blocks (pass/fail) ---
TEST(ParserAnnexF, AnnexFAssertActionBlocks) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b)\n"
      "    $display(\"PASS\");\n"
      "  else\n"
      "    $error(\"FAIL\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssertProperty) {
      found = true;
      EXPECT_NE(item->assert_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

// --- F.20: Unbounded delay range ##[0:$] ---
TEST(ParserAnnexF, AnnexFUnboundedDelayRange) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ##[0:$] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// =============================================================================
// Annex G -- Std package classes (process, semaphore, mailbox)
// =============================================================================

TEST(ParserAnnexG, AnnexGProcessDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserAnnexG, AnnexGSemaphoreUsage) {
  auto r = Parse(
      "module m;\n"
      "  semaphore sem = new(1);\n"
      "  initial begin\n"
      "    sem.get();\n"
      "    sem.put();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserAnnexG, AnnexGMailboxUsage) {
  auto r = Parse(
      "module m;\n"
      "  mailbox #(int) mb = new();\n"
      "  initial begin\n"
      "    mb.put(42);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// =============================================================================
// Annex N -- Probabilistic distribution functions
// =============================================================================

TEST(ParserAnnexN, AnnexNDistUniform) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $dist_uniform(seed, 0, 100);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserAnnexN, AnnexNDistNormal) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $dist_normal(seed, 50, 10);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserAnnexN, AnnexNDistExponential) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $dist_exponential(seed, 5);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserAnnexN, AnnexNDistPoisson) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $dist_poisson(seed, 10);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserAnnexN, AnnexNDistChiSquare) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $dist_chi_square(seed, 3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}
