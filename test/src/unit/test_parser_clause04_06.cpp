// Tests for IEEE 1800 LRM §4.6 — Determinism
//
// Verifies that all syntactic constructs related to determinism guarantees
// parse correctly: always_comb/always_ff/always_latch, unique/priority/unique0
// case and if, program blocks, blocking vs non-blocking, fork/join variants,
// variable lifetime qualifiers, and port connection styles.

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult4c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4c Parse(const std::string& src) {
  ParseResult4c result;
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

static ModuleItem* FirstItem(ParseResult4c& r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

// Returns the first always_* item from the first module.
static ModuleItem* FirstAlwaysItem(ParseResult4c& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock)
      return item;
  }
  return nullptr;
}

// Returns the first statement inside the first initial block's begin-end.
static Stmt* FirstInitialStmt(ParseResult4c& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

// Returns the body of the first initial block.
static Stmt* InitialBody(ParseResult4c& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) return item->body;
  }
  return nullptr;
}

static bool HasDefaultCaseItem(const Stmt* case_stmt) {
  for (const auto& ci : case_stmt->case_items) {
    if (ci.is_default) return true;
  }
  return false;
}

// =============================================================================
// §4.6: always_comb guarantees combinational semantics
// =============================================================================

TEST(ParserSection4, Sec4_6_AlwaysCombCombinational) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, y;\n"
      "  always_comb begin\n"
      "    y = a & b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
}

// =============================================================================
// §4.6: always_ff guarantees flip-flop semantics
// =============================================================================

TEST(ParserSection4, Sec4_6_AlwaysFfFlipFlop) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always_ff @(posedge clk) begin\n"
      "    q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
}

// =============================================================================
// §4.6: always_latch guarantees latch semantics
// =============================================================================

TEST(ParserSection4, Sec4_6_AlwaysLatchLatch) {
  auto r = Parse(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch begin\n"
      "    if (en) q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
  ASSERT_NE(item->body, nullptr);
}

// =============================================================================
// §4.6: unique case statement — exactly one match expected
// =============================================================================

TEST(ParserSection4, Sec4_6_UniqueCaseOneMatch) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique case (sel)\n"
      "      2'b00: y = 0;\n"
      "      2'b01: y = 1;\n"
      "      2'b10: y = 2;\n"
      "      2'b11: y = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

// =============================================================================
// §4.6: unique0 case statement — at most one match
// =============================================================================

TEST(ParserSection4, Sec4_6_Unique0CaseAtMostOneMatch) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique0 case (sel)\n"
      "      0: x = 1;\n"
      "      1: x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

// =============================================================================
// §4.6: priority case statement — first match
// =============================================================================

TEST(ParserSection4, Sec4_6_PriorityCaseFirstMatch) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority case (sel)\n"
      "      0: x = 1;\n"
      "      1: x = 2;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

// =============================================================================
// §4.6: unique if statement
// =============================================================================

TEST(ParserSection4, Sec4_6_UniqueIf) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "    else x = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

// =============================================================================
// §4.6: unique0 if statement
// =============================================================================

TEST(ParserSection4, Sec4_6_Unique0If) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique0 if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

// =============================================================================
// §4.6: priority if statement
// =============================================================================

TEST(ParserSection4, Sec4_6_PriorityIf) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "    else x = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

// =============================================================================
// §4.6: Program block for deterministic test scheduling
// =============================================================================

TEST(ParserSection4, Sec4_6_ProgramBlockDeterministicScheduling) {
  auto r = Parse(
      "program p;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "p");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

// =============================================================================
// §4.6: Program block with initial block
// =============================================================================

TEST(ParserSection4, Sec4_6_ProgramWithInitialBlock) {
  auto r = Parse(
      "program p;\n"
      "  initial begin\n"
      "    $display(\"test\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ASSERT_EQ(r.cu->programs[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
}

// =============================================================================
// §4.6: Program block with final block
// =============================================================================

TEST(ParserSection4, Sec4_6_ProgramWithFinalBlock) {
  auto r = Parse(
      "program p;\n"
      "  final begin\n"
      "    $display(\"done\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ASSERT_EQ(r.cu->programs[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
}

// =============================================================================
// §4.6: Blocking assignment ordering — sequential within block
// =============================================================================

TEST(ParserSection4, Sec4_6_BlockingAssignOrdering) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = a;\n"
      "    c = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kBlockingAssign);
}

// =============================================================================
// §4.6: Non-blocking assignment ordering
// =============================================================================

TEST(ParserSection4, Sec4_6_NonblockingAssignOrdering) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <= 1;\n"
      "    b <= 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kNonblockingAssign);
}

// =============================================================================
// §4.6: Named begin-end block for deterministic scoping
// =============================================================================

TEST(ParserSection4, Sec4_6_NamedBeginEndScope) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : seq_blk\n"
      "    x = 1;\n"
      "    y = 2;\n"
      "  end : seq_blk\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "seq_blk");
}

// =============================================================================
// §4.6: Ordered (positional) port connections — deterministic mapping
// =============================================================================

TEST(ParserSection4, Sec4_6_OrderedPortConnections) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (a, b, c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  ASSERT_EQ(item->inst_ports.size(), 3u);
  // Positional ports have empty name (first element of pair).
  EXPECT_TRUE(item->inst_ports[0].first.empty());
  EXPECT_TRUE(item->inst_ports[1].first.empty());
  EXPECT_TRUE(item->inst_ports[2].first.empty());
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_NE(item->inst_ports[1].second, nullptr);
  EXPECT_NE(item->inst_ports[2].second, nullptr);
}

// =============================================================================
// §4.6: Named port connections — deterministic mapping
// =============================================================================

TEST(ParserSection4, Sec4_6_NamedPortConnections) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.clk(clk), .rst(rst), .d(data));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  ASSERT_EQ(item->inst_ports.size(), 3u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
  EXPECT_EQ(item->inst_ports[2].first, "d");
}

// =============================================================================
// §4.6: Variable initialization at declaration — static lifetime determinism
// =============================================================================

TEST(ParserSection4, Sec4_6_VarInitAtDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  int x = 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_NE(item->init_expr, nullptr);
}

// =============================================================================
// §4.6: Automatic variable initialization per entry
// =============================================================================

TEST(ParserSection4, Sec4_6_AutomaticVarInitPerEntry) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int count = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->var_is_automatic);
  EXPECT_NE(stmt->var_init, nullptr);
}

// =============================================================================
// §4.6: always_comb with case inside
// =============================================================================

TEST(ParserSection4, Sec4_6_AlwaysCombWithCaseInside) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb begin\n"
      "    case (sel)\n"
      "      2'b00: y = 4'h0;\n"
      "      2'b01: y = 4'h1;\n"
      "      2'b10: y = 4'h2;\n"
      "      default: y = 4'hf;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kCase);
}

// =============================================================================
// §4.6: always_ff with if-else chain
// =============================================================================

TEST(ParserSection4, Sec4_6_AlwaysFfWithIfElseChain) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, rst, d, q;\n"
      "  always_ff @(posedge clk or posedge rst) begin\n"
      "    if (rst) q <= 0;\n"
      "    else q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kIf);
}

// =============================================================================
// §4.6: always_latch with if (no else)
// =============================================================================

TEST(ParserSection4, Sec4_6_AlwaysLatchIfNoElse) {
  auto r = Parse(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch\n"
      "    if (en) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
  EXPECT_EQ(item->body->else_branch, nullptr);
}

// =============================================================================
// §4.6: Fork-join ordering — all branches complete
// =============================================================================

TEST(ParserSection4, Sec4_6_ForkJoinAllComplete) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  join\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->join_kind, TokenKind::kKwJoin);
}

// =============================================================================
// §4.6: Fork-join_any ordering — first branch completes
// =============================================================================

TEST(ParserSection4, Sec4_6_ForkJoinAnyFirstComplete) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  join_any\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->join_kind, TokenKind::kKwJoinAny);
}

// =============================================================================
// §4.6: Fork-join_none ordering — all branches concurrent
// =============================================================================

TEST(ParserSection4, Sec4_6_ForkJoinNoneConcurrent) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  join_none\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->join_kind, TokenKind::kKwJoinNone);
}

// =============================================================================
// §4.6: Priority case with default
// =============================================================================

TEST(ParserSection4, Sec4_6_PriorityCaseWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority case (opcode)\n"
      "      4'h0: result = a + b;\n"
      "      4'h1: result = a - b;\n"
      "      4'h2: result = a & b;\n"
      "      default: result = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
  EXPECT_TRUE(HasDefaultCaseItem(stmt));
}

// =============================================================================
// §4.6: Unique case with multiple matches listed
// =============================================================================

TEST(ParserSection4, Sec4_6_UniqueCaseMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique case (state)\n"
      "      IDLE: x = 0;\n"
      "      RUN: x = 1;\n"
      "      DONE: x = 2;\n"
      "      ERR: x = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
  EXPECT_EQ(stmt->case_items.size(), 4u);
}

// =============================================================================
// §4.6: always_comb with multiple outputs
// =============================================================================

TEST(ParserSection4, Sec4_6_AlwaysCombMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, sum, carry;\n"
      "  always_comb begin\n"
      "    sum = a ^ b;\n"
      "    carry = a & b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_GE(item->body->stmts.size(), 2u);
}

// =============================================================================
// §4.6: Program block with clocking block reference
// =============================================================================

TEST(ParserSection4, Sec4_6_ProgramWithClockingBlock) {
  EXPECT_TRUE(
      ParseOk("program p(input logic clk);\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "    output valid;\n"
              "  endclocking\n"
              "  initial begin\n"
              "    @(cb);\n"
              "    $display(\"synced\");\n"
              "  end\n"
              "endprogram\n"));
}

// =============================================================================
// §4.6: Static vs automatic function lifetime
// =============================================================================

TEST(ParserSection4, Sec4_6_StaticVsAutomaticFunctionLifetime) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int auto_fn();\n"
      "    return 1;\n"
      "  endfunction\n"
      "  function static int static_fn();\n"
      "    return 2;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* auto_fn = r.cu->modules[0]->items[0];
  auto* static_fn = r.cu->modules[0]->items[1];
  EXPECT_EQ(auto_fn->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(auto_fn->is_automatic);
  EXPECT_FALSE(auto_fn->is_static);
  EXPECT_EQ(static_fn->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(static_fn->is_static);
  EXPECT_FALSE(static_fn->is_automatic);
}
