#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

bool ParseOk(const std::string &src) {
  auto r = Parse(src);
  return r.cu && !r.has_errors;
}

} // namespace

// =============================================================================
// A.2.2.3 Delays
// =============================================================================

// ---------------------------------------------------------------------------
// delay_value ::= unsigned_number | real_number | ps_identifier
//               | time_literal | 1step
// ---------------------------------------------------------------------------

// delay_value: unsigned_number — integer literal as delay value.
TEST(ParserA223, DelayValueUnsignedNumber) {
  auto r = Parse("module m;\n"
                 "  wire #10 w;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(item->net_delay->int_val, 10u);
}

// delay_value: real_number — real literal as delay value.
TEST(ParserA223, DelayValueRealNumber) {
  auto r = Parse("module m;\n"
                 "  wire #1.5 w;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kRealLiteral);
}

// delay_value: ps_identifier — parameter/specparam identifier as delay.
TEST(ParserA223, DelayValuePsIdentifier) {
  auto r = Parse("module m;\n"
                 "  parameter delay_val = 5;\n"
                 "  wire #delay_val w;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // items[0] is the parameter, items[1] is the wire
  auto *item = r.cu->modules[0]->items[1];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kIdentifier);
}

// delay_value: time_literal — time literal (e.g. 10ns) as delay.
TEST(ParserA223, DelayValueTimeLiteral) {
  auto r = Parse("module m;\n"
                 "  wire #10ns w;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kTimeLiteral);
}

// delay_value: 1step — special keyword in clocking context.
TEST(ParserA223, DelayValue1step) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  clocking cb @(posedge clk);\n"
                      "    input #1step data;\n"
                      "  endclocking\n"
                      "endmodule"));
}

// ---------------------------------------------------------------------------
// delay3 ::= # delay_value
//          | # ( mintypmax_expression
//                [, mintypmax_expression [, mintypmax_expression]] )
// ---------------------------------------------------------------------------

// --- delay3 on net declarations ---

// delay3: single value on net declaration (# delay_value form).
TEST(ParserA223, Delay3NetSingleValue) {
  auto r = Parse("module m;\n"
                 "  wire #5 w;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 5u);
  EXPECT_EQ(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

// delay3: two values on net (rise, fall).
TEST(ParserA223, Delay3NetTwoValues) {
  auto r = Parse("module m;\n"
                 "  wire #(10, 20) w;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 10u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 20u);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

// delay3: three values on net (rise, fall, charge_decay).
TEST(ParserA223, Delay3NetThreeValues) {
  auto r = Parse("module m;\n"
                 "  wire #(10, 20, 30) w;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 10u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 20u);
  ASSERT_NE(item->net_delay_decay, nullptr);
  EXPECT_EQ(item->net_delay_decay->int_val, 30u);
}

// delay3: mintypmax expression in parenthesized form.
TEST(ParserA223, Delay3NetMintypmax) {
  auto r = Parse("module m;\n"
                 "  wire #(1:2:3) w;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kMinTypMax);
}

// --- delay3 on gate instantiations ---

// delay3: single value on gate (# delay_value form).
TEST(ParserA223, Delay3GateSingleValue) {
  auto r = Parse("module m;\n"
                 "  wire y, a, b;\n"
                 "  and #5 g1(y, a, b);\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // wire y, a, b creates 3 items; gate is items[3]
  auto *item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 5u);
  EXPECT_EQ(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_decay, nullptr);
}

// delay3: two values on gate (rise, fall).
TEST(ParserA223, Delay3GateTwoValues) {
  auto r = Parse("module m;\n"
                 "  wire y, a, b;\n"
                 "  and #(10, 20) g1(y, a, b);\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 10u);
  ASSERT_NE(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_fall->int_val, 20u);
  EXPECT_EQ(item->gate_delay_decay, nullptr);
}

// delay3: three values on gate (rise, fall, turn-off).
TEST(ParserA223, Delay3GateThreeValues) {
  auto r = Parse("module m;\n"
                 "  wire y, a, b;\n"
                 "  bufif1 #(10, 20, 30) g1(y, a, b);\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 10u);
  ASSERT_NE(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_fall->int_val, 20u);
  ASSERT_NE(item->gate_delay_decay, nullptr);
  EXPECT_EQ(item->gate_delay_decay->int_val, 30u);
}

// delay3: mintypmax on gate — #(1:2:3) with min:typ:max expression.
TEST(ParserA223, Delay3GateMintypmax) {
  auto r = Parse("module m;\n"
                 "  wire y, a, b;\n"
                 "  and #(1:2:3) g1(y, a, b);\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->kind, ExprKind::kMinTypMax);
}

// --- delay3 on continuous assignments ---

// delay3: single value on continuous assign.
TEST(ParserA223, Delay3AssignSingleValue) {
  auto r = Parse("module m;\n"
                 "  wire out, in;\n"
                 "  assign #5 out = in;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[2];
  ASSERT_NE(item->assign_delay, nullptr);
  EXPECT_EQ(item->assign_delay->int_val, 5u);
  EXPECT_EQ(item->assign_delay_fall, nullptr);
  EXPECT_EQ(item->assign_delay_decay, nullptr);
}

// delay3: two values on continuous assign (rise, fall).
TEST(ParserA223, Delay3AssignTwoValues) {
  auto r = Parse("module m;\n"
                 "  wire out, in;\n"
                 "  assign #(10, 20) out = in;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[2];
  ASSERT_NE(item->assign_delay, nullptr);
  EXPECT_EQ(item->assign_delay->int_val, 10u);
  ASSERT_NE(item->assign_delay_fall, nullptr);
  EXPECT_EQ(item->assign_delay_fall->int_val, 20u);
  EXPECT_EQ(item->assign_delay_decay, nullptr);
}

// delay3: three values on continuous assign (rise, fall, charge_decay).
TEST(ParserA223, Delay3AssignThreeValues) {
  auto r = Parse("module m;\n"
                 "  wire out, in;\n"
                 "  assign #(10, 20, 30) out = in;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[2];
  ASSERT_NE(item->assign_delay, nullptr);
  EXPECT_EQ(item->assign_delay->int_val, 10u);
  ASSERT_NE(item->assign_delay_fall, nullptr);
  EXPECT_EQ(item->assign_delay_fall->int_val, 20u);
  ASSERT_NE(item->assign_delay_decay, nullptr);
  EXPECT_EQ(item->assign_delay_decay->int_val, 30u);
}

// ---------------------------------------------------------------------------
// delay2 ::= # delay_value
//          | # ( mintypmax_expression [, mintypmax_expression] )
// ---------------------------------------------------------------------------

// delay2: single value on n_input gate (uses delay2 per BNF).
TEST(ParserA223, Delay2NInputGateSingleValue) {
  auto r = Parse("module m;\n"
                 "  wire y, a, b;\n"
                 "  xor #7 g1(y, a, b);\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 7u);
}

// delay2: two values on n_input gate (rise, fall).
TEST(ParserA223, Delay2NInputGateTwoValues) {
  auto r = Parse("module m;\n"
                 "  wire y, a, b;\n"
                 "  or #(3, 5) g1(y, a, b);\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 3u);
  ASSERT_NE(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_fall->int_val, 5u);
}

// delay2: parenthesized single value — #(expr).
TEST(ParserA223, Delay2ParenSingleValue) {
  auto r = Parse("module m;\n"
                 "  wire out, in;\n"
                 "  assign #(5) out = in;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[2];
  ASSERT_NE(item->assign_delay, nullptr);
  EXPECT_EQ(item->assign_delay->int_val, 5u);
}

// delay2: mintypmax expression in parenthesized form.
TEST(ParserA223, Delay2MintypMaxSingleValue) {
  auto r = Parse("module m;\n"
                 "  wire out, in;\n"
                 "  assign #(1:2:3) out = in;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[2];
  ASSERT_NE(item->assign_delay, nullptr);
  EXPECT_EQ(item->assign_delay->kind, ExprKind::kMinTypMax);
}

// ---------------------------------------------------------------------------
// Delay propagation across multiple instances
// ---------------------------------------------------------------------------

// Gate delay shared across comma-separated instances.
TEST(ParserA223, Delay3GateMultipleInstances) {
  auto r = Parse("module m;\n"
                 "  wire y1, y2, a, b;\n"
                 "  and #(4, 6) g1(y1, a, b), g2(y2, a, b);\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // wire y1, y2, a, b creates 4 items; gates are items[4] and items[5]
  auto *g1 = r.cu->modules[0]->items[4];
  auto *g2 = r.cu->modules[0]->items[5];
  ASSERT_NE(g1->gate_delay, nullptr);
  EXPECT_EQ(g1->gate_delay->int_val, 4u);
  ASSERT_NE(g1->gate_delay_fall, nullptr);
  EXPECT_EQ(g1->gate_delay_fall->int_val, 6u);
  ASSERT_NE(g2->gate_delay, nullptr);
  EXPECT_EQ(g2->gate_delay->int_val, 4u);
  ASSERT_NE(g2->gate_delay_fall, nullptr);
  EXPECT_EQ(g2->gate_delay_fall->int_val, 6u);
}

// No delay specified — fields remain nullptr.
TEST(ParserA223, NoDelayDefault) {
  auto r = Parse("module m;\n"
                 "  wire w;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

// Statement delay: #delay_value in procedural context.
TEST(ParserA223, DelayValueInStatement) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  initial #10 $display(\"hello\");\n"
                      "endmodule"));
}

// Intra-assignment delay: var = #delay expr.
TEST(ParserA223, IntraAssignmentDelay) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  reg r;\n"
                      "  initial r = #5 1'b1;\n"
                      "endmodule"));
}

// Time literal variants in delay: fs, ps, ns, us, ms, s.
TEST(ParserA223, DelayValueAllTimeLiterals) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  wire #1fs w1;\n"
                      "  wire #2ps w2;\n"
                      "  wire #3ns w3;\n"
                      "  wire #4us w4;\n"
                      "  wire #5ms w5;\n"
                      "  wire #6s w6;\n"
                      "endmodule"));
}
