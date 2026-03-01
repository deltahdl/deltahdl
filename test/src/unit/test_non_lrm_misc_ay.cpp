// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

namespace {

TEST(ParserAnnexD, AnnexDScope) {
  auto r = Parse(
      "module m;\n"
      "  initial begin $scope(m); $showscopes; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
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

}  // namespace
