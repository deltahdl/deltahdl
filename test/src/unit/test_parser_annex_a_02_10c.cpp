#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- property_expr: parenthesized, sequence_expr ---

TEST(AssertionDeclParsing, PropertyExpr_Parenthesized) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) (a |-> b));\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_SequenceExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##1 b);\n"
              "endmodule\n"));
}

// --- property_expr: strong / weak ---

TEST(AssertionDeclParsing, PropertyExpr_Strong) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) strong(a ##1 b));\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_Weak) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) weak(a ##1 b));\n"
              "endmodule\n"));
}

TEST(AssertionParsing, StrongSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) strong(a ##1 b ##1 c));\n"
              "endmodule\n"));
}

TEST(AssertionParsing, WeakSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) weak(a ##1 b));\n"
              "endmodule\n"));
}

TEST(AssertionParsing, StrongSequenceProperty) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) strong(a ##1 b ##1 c));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionParsing, WeakSequenceProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) weak(a ##1 b));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// --- property_expr: not ---

TEST(AssertionDeclParsing, PropertyExpr_Not) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) not a);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, PropertyNot) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) not (a ##1 b));\n"
              "endmodule\n"));
}

TEST(AssertionParsing, PropertyNegation) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) not (a ##1 b));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionParsing, PropertyNegationStrong) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) not strong(a ##1 b));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// --- property_expr: or ---

TEST(AssertionDeclParsing, PropertyExpr_Or) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a or b);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, PropertyOr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) (a |-> b) or (c |-> d));\n"
              "endmodule\n"));
}

TEST(AssertionParsing, PropertyDisjunction) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a |-> b) or (c |-> d));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionParsing, PropertyDisjunctionAndConjunctionCombined) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk)\n"
      "    ((a |-> b) and (c |-> d)) or (e |-> f));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// --- property_expr: and ---

TEST(AssertionDeclParsing, PropertyExpr_And) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a and b);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, PropertyConjunction) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a |-> b) and (c |-> d));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// --- property_expr: if / else ---

TEST(AssertionDeclParsing, PropertyExpr_IfElse) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    if (mode) a |-> b else c |-> d);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_IfNoElse) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    if (mode) a |-> b);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, PropertyIfElse) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk)\n"
              "    if (mode) a |-> b\n"
              "    else a |-> c);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, PropertyIfElseParseResult) {
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

TEST(AssertionParsing, PropertyIfWithoutElse) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk)\n"
      "    if (en) a |-> ##[1:3] b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionParsing, PropertyIfElseInDecl) {
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

// --- property_expr: implication |-> |=> ---

TEST(AssertionDeclParsing, PropertyExpr_OverlappedImplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) req |-> ack);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_NonOverlappedImplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) req |=> ack);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceInstance_InProperty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##1 b; endsequence\n"
              "  property p; s |-> c; endproperty\n"
              "  assert property (p);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, AssertPropertyOverlappedImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

TEST(AssertionParsing, AssertPropertyNonOverlappedImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |=> gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

TEST(AssertionParsing, PropertyOverlappedImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionParsing, PropertyNonOverlappedImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |=> gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionParsing, SequenceUsedInPropertyDecl) {
  auto r = Parse(
      "module m;\n"
      "  sequence s1;\n"
      "    a ##1 b;\n"
      "  endsequence\n"
      "  property p1;\n"
      "    @(posedge clk) s1 |=> c;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- property_expr: implies, iff ---

TEST(AssertionDeclParsing, PropertyExpr_Implies) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a implies b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_Iff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a iff b);\n"
              "endmodule\n"));
}

// --- property_expr: #-# #=# ---

TEST(AssertionDeclParsing, PropertyExpr_FollowedByOverlapped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a #-# b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_FollowedByNonOverlapped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a #=# b);\n"
              "endmodule\n"));
}

// --- property_expr: nexttime, s_nexttime ---

TEST(AssertionDeclParsing, PropertyExpr_Nexttime) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) nexttime a);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_NexttimeWithCount) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) nexttime [3] a);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_SNexttime) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_nexttime a);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_SNexttimeWithCount) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_nexttime [2] a);\n"
              "endmodule\n"));
}

// --- property_expr: always, s_always ---

TEST(AssertionDeclParsing, PropertyExpr_Always) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) always a);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_AlwaysRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) always [0:5] a);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_SAlways) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_always [0:$] a);\n"
              "endmodule\n"));
}

// --- property_expr: until, s_until, until_with, s_until_with ---

TEST(AssertionDeclParsing, PropertyExpr_Until) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a until b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_SUntil) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a s_until b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_UntilWith) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a until_with b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_SUntilWith) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a s_until_with b);\n"
              "endmodule\n"));
}

// --- property_expr: eventually, s_eventually ---

TEST(AssertionDeclParsing, PropertyExpr_SEventually) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_eventually a);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_SEventuallyRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_eventually [1:5] a);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_Eventually) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) eventually [1:5] a);\n"
              "endmodule\n"));
}

// --- property_expr: accept_on, reject_on, sync_accept_on, sync_reject_on ---

TEST(AssertionDeclParsing, PropertyExpr_AcceptOn) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  assert property (@(posedge clk) accept_on(done) req |-> ack);\n"
      "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_RejectOn) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) reject_on(err) req |-> ack);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_SyncAcceptOn) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) sync_accept_on(done) req |-> ack);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_SyncRejectOn) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) sync_reject_on(err) req |-> ack);\n"
              "endmodule\n"));
}

// --- property_expr: case ---

TEST(AssertionDeclParsing, PropertyExpr_Case) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    case (sel)\n"
              "      2'b00: a |-> b;\n"
              "      2'b01: c |-> d;\n"
              "      default: 1;\n"
              "    endcase);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyCaseItem_MultiExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    case (sel)\n"
              "      2'b00, 2'b01: a |-> b;\n"
              "      default: 1;\n"
              "    endcase);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyCaseItem_DefaultOnly) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    case (sel)\n"
              "      default: a;\n"
              "    endcase);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyCaseItem_DefaultNoColon) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    case (sel)\n"
              "      2'b00: a |-> b;\n"
              "      default a;\n"
              "    endcase);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, PropertyCaseWithDefaultOnly) {
  auto r = Parse(
      "module m;\n"
      "  property p_mode;\n"
      "    case (mode)\n"
      "      default: a |-> b;\n"
      "    endcase\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, PropertyCaseBasic) {
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

TEST(AssertionParsing, PropertyCaseInAssert) {
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

// --- property_expr: clocking_event ---

TEST(AssertionDeclParsing, PropertyExpr_ClockingEventPropertyExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) a |-> @(posedge clk2) b);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, MulticlockAssertPropertyInline) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk1) a ##1 @(posedge clk2) b\n"
      "  );\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, MulticlockPropertyDeclImplication) {
  auto r = Parse(
      "module m;\n"
      "  property p_multi;\n"
      "    @(posedge clk1) req |=> @(posedge clk2) ack;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
