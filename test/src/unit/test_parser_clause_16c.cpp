#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult16c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult16c Parse(const std::string &src) {
  ParseResult16c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem *FindItemByKind(const std::vector<ModuleItem *> &items,
                                  ModuleItemKind kind) {
  for (auto *item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

static size_t CountItemsByKind(const std::vector<ModuleItem *> &items,
                               ModuleItemKind kind) {
  size_t count = 0;
  for (auto *item : items) {
    if (item->kind == kind) ++count;
  }
  return count;
}

// =============================================================================
// Section 16.5.1 -- Concurrent assertion statements: assert property
// =============================================================================

// Assert property with a simple property expression (no clock, no implication).
TEST(ParserSection16, Sec16_5_1_AssertPropertySimple) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a && b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto *ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

// Assert property with a posedge-clocked property.
TEST(ParserSection16, Sec16_5_1_AssertPropertyClockedPosedge) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto *ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

// Assert property with overlapped implication (|->).
TEST(ParserSection16, Sec16_5_1_AssertPropertyOverlappedImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto *ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

// Assert property with non-overlapped implication (|=>).
TEST(ParserSection16, Sec16_5_1_AssertPropertyNonOverlappedImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |=> gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto *ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

// Assert property with both pass and fail action blocks.
TEST(ParserSection16, Sec16_5_1_AssertPropertyPassAndFailActions) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack)\n"
      "    $display(\"pass\"); else $error(\"fail\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto *ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_pass_stmt, nullptr);
  EXPECT_NE(ap->assert_fail_stmt, nullptr);
}

// Assert property with only a pass action (no else).
TEST(ParserSection16, Sec16_5_1_AssertPropertyPassOnly) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) valid)\n"
      "    $display(\"passed\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto *ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_pass_stmt, nullptr);
  EXPECT_EQ(ap->assert_fail_stmt, nullptr);
}

// Assert property with only an else (fail) action.
TEST(ParserSection16, Sec16_5_1_AssertPropertyFailOnly) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b)\n"
      "    else $error(\"failed\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto *ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_EQ(ap->assert_pass_stmt, nullptr);
  EXPECT_NE(ap->assert_fail_stmt, nullptr);
}

// =============================================================================
// Section 16.5.1 -- Concurrent assertion statements: assume property
// =============================================================================

// Assume property with a simple property expression.
TEST(ParserSection16, Sec16_5_1_AssumePropertySimple) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) valid);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto *ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

// Assume property with a clocked implication.
TEST(ParserSection16, Sec16_5_1_AssumePropertyClocked) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |-> gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto *ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

// Assume property with else action.
TEST(ParserSection16, Sec16_5_1_AssumePropertyElseAction) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) en |-> ready)\n"
      "    else $error(\"assumption violated\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto *ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_EQ(ap->assert_pass_stmt, nullptr);
  EXPECT_NE(ap->assert_fail_stmt, nullptr);
}

// =============================================================================
// Section 16.5.1 -- Concurrent assertion statements: cover property
// =============================================================================

// Cover property with a simple clocked property.
TEST(ParserSection16, Sec16_5_1_CoverPropertySimple) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a && b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto *cp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(cp, nullptr);
  EXPECT_NE(cp->assert_expr, nullptr);
}

// Cover property with a clocked sequence delay.
TEST(ParserSection16, Sec16_5_1_CoverPropertyClocked) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto *cp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(cp, nullptr);
  EXPECT_NE(cp->assert_expr, nullptr);
}

// Cover property with a pass action (cover has no else branch per LRM).
TEST(ParserSection16, Sec16_5_1_CoverPropertyPassAction) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b)\n"
      "    $display(\"covered\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto *cp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(cp, nullptr);
  EXPECT_NE(cp->assert_pass_stmt, nullptr);
}

// =============================================================================
// Section 16.5.1 -- Concurrent assertion statements: cover sequence
// The parser routes cover sequence through cover property (kCoverProperty).
// =============================================================================

// Cover sequence-like pattern with pass action via cover property.
TEST(ParserSection16, Sec16_5_1_CoverSequenceWithPassAction) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##2 b ##1 c)\n"
      "    $display(\"seq covered\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto *cp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(cp, nullptr);
  EXPECT_NE(cp->assert_pass_stmt, nullptr);
}

// =============================================================================
// Section 16.5.1 -- Named concurrent assertions (label: assert property)
// Named assertions in procedural context use statement labels.
// =============================================================================

// Named assert property inside an always block.
TEST(ParserSection16, Sec16_5_1_NamedAssertInAlways) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @(posedge clk) begin\n"
              "    check_req: assert property (req |-> ack);\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// Section 16.5.1 -- disable iff in concurrent assertions
// =============================================================================

// Assert property with disable iff.
TEST(ParserSection16, Sec16_5_1_AssertPropertyDisableIff) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) disable iff (rst) req |-> ack);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto *ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

// =============================================================================
// Section 16.5.1 -- Sequence operators in concurrent assertions
// =============================================================================

// Assert property with ## cycle delay operator.
TEST(ParserSection16, Sec16_5_1_SequenceDelayOperator) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) req ##1 gnt ##1 !req);\n"
              "endmodule\n"));
}

// Assert property with [*N] consecutive repetition.
TEST(ParserSection16, Sec16_5_1_SequenceConsecutiveRepetition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a[*3] |-> b);\n"
              "endmodule\n"));
}

// Assert property with [->N] goto repetition.
TEST(ParserSection16, Sec16_5_1_SequenceGotoRepetition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) req |-> ack[->1]);\n"
              "endmodule\n"));
}

// Assert property with throughout operator.
TEST(ParserSection16, Sec16_5_1_SequenceThroughout) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) !burst throughout (##2 trdy[*7]));\n"
              "endmodule\n"));
}

// =============================================================================
// Section 16.5.1 -- Property operators in concurrent assertions
// =============================================================================

// Assert property with not (property negation).
TEST(ParserSection16, Sec16_5_1_PropertyNot) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) not (a ##1 b));\n"
              "endmodule\n"));
}

// Assert property with or (disjunction).
TEST(ParserSection16, Sec16_5_1_PropertyOr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) (a |-> b) or (c |-> d));\n"
              "endmodule\n"));
}

// Assert property with if-else inside property expression.
TEST(ParserSection16, Sec16_5_1_PropertyIfElse) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk)\n"
              "    if (mode) a |-> b\n"
              "    else a |-> c);\n"
              "endmodule\n"));
}

// =============================================================================
// Section 16.5.1 -- Strong and weak sequences
// =============================================================================

// Assert property with strong sequence.
TEST(ParserSection16, Sec16_5_1_StrongSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) strong(a ##1 b ##1 c));\n"
              "endmodule\n"));
}

// Assert property with weak sequence.
TEST(ParserSection16, Sec16_5_1_WeakSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) weak(a ##1 b));\n"
              "endmodule\n"));
}

// =============================================================================
// Section 16.5.1 -- Multiple concurrent assertions in same module
// =============================================================================

// Multiple assert/assume/cover property items in one module.
TEST(ParserSection16, Sec16_5_1_MultipleConcurrentAssertions) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "  assume property (@(posedge clk) en);\n"
      "  cover property (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(CountItemsByKind(r.cu->modules[0]->items,
                             ModuleItemKind::kAssertProperty),
            1u);
  EXPECT_EQ(CountItemsByKind(r.cu->modules[0]->items,
                             ModuleItemKind::kAssumeProperty),
            1u);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty),
      1u);
}

// =============================================================================
// Section 16.5.1 -- Concurrent assertions in procedural context
// =============================================================================

// Assert property inside an always block (procedural concurrent assertion).
TEST(ParserSection16, Sec16_5_1_AssertPropertyInAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @(posedge clk) begin\n"
              "    assert property (req |-> ack);\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// Section 16.5.1 -- Assert property with named property instance
// =============================================================================

// Assert property referencing a previously declared named property.
TEST(ParserSection16, Sec16_5_1_AssertWithNamedPropertyInstance) {
  auto r = Parse(
      "module m;\n"
      "  property p_handshake;\n"
      "    @(posedge clk) req |-> ##[1:3] ack;\n"
      "  endproperty\n"
      "  assert property (p_handshake);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto *pd =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->name, "p_handshake");
  auto *ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

// =============================================================================
// Section 16.5.1 -- Assert property with sequence methods
// =============================================================================

// Sequence .triggered method used in a sequence declaration.
TEST(ParserSection16, Sec16_5_1_SequenceTriggeredMethod) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s1;\n"
              "    @(posedge clk) a ##1 b;\n"
              "  endsequence\n"
              "  sequence s2;\n"
              "    @(posedge clk) c ##1 s1.triggered ##1 d;\n"
              "  endsequence\n"
              "endmodule\n"));
}

// Sequence .matched method used across clock domains.
TEST(ParserSection16, Sec16_5_1_SequenceMatchedMethod) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence e1;\n"
              "    @(posedge clk1) a ##1 b;\n"
              "  endsequence\n"
              "  sequence e2;\n"
              "    @(posedge clk2) c ##1 e1.matched ##1 d;\n"
              "  endsequence\n"
              "endmodule\n"));
}
