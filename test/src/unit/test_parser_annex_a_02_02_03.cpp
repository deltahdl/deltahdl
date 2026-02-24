// Annex A.2.2.3: Delays

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

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

namespace {

// =============================================================================
// A.2.2.3 Delays
// =============================================================================
// ---------------------------------------------------------------------------
// delay_value ::= unsigned_number | real_number | ps_identifier
//               | time_literal | 1step
// ---------------------------------------------------------------------------
// delay_value: unsigned_number — integer literal as delay value.
TEST(ParserA223, DelayValueUnsignedNumber) {
  auto r = Parse(
      "module m;\n"
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
  auto r = Parse(
      "module m;\n"
      "  wire #1.5 w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kRealLiteral);
}

// delay3: two values on net (rise, fall).
TEST(ParserA223, Delay3NetTwoValues) {
  auto r = Parse(
      "module m;\n"
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
  auto r = Parse(
      "module m;\n"
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

// --- delay3 on gate instantiations ---
// delay3: single value on gate (# delay_value form).
TEST(ParserA223, Delay3GateSingleValue) {
  auto r = Parse(
      "module m;\n"
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
  auto r = Parse(
      "module m;\n"
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

// delay3: two values on continuous assign (rise, fall).
TEST(ParserA223, Delay3AssignTwoValues) {
  auto r = Parse(
      "module m;\n"
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

// ---------------------------------------------------------------------------
// delay2 ::= # delay_value
//          | # ( mintypmax_expression [, mintypmax_expression] )
// ---------------------------------------------------------------------------
// delay2: single value on n_input gate (uses delay2 per BNF).
TEST(ParserA223, Delay2NInputGateSingleValue) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  xor #7 g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 7u);
}

// No delay specified — fields remain nullptr.
TEST(ParserA223, NoDelayDefault) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

}  // namespace
