// Annex A.3.3: Primitive terminals

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.3.3 Production #1: enable_terminal ::= expression
// Exercised via enable gates (bufif0/bufif1/notif0/notif1) and
// pass enable switches (tranif0/tranif1/rtranif0/rtranif1).
// The enable_terminal is the third terminal in these gate instances.
// =============================================================================
TEST(ParserA303, EnableTerminal_SimpleIdent) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA303, EnableTerminal_ComplexExpr) {
  // enable_terminal accepts any expression
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bufif1 (out, in, a & b);\n"
              "endmodule\n"));
}

TEST(ParserA303, EnableTerminal_BitwiseExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  notif0 (out, in, a | b | c);\n"
              "endmodule\n"));
}

TEST(ParserA303, EnableTerminal_TernaryExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  notif1 (out, in, sel ? en1 : en2);\n"
              "endmodule\n"));
}

TEST(ParserA303, EnableTerminal_BitSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bufif0 (out, in, ctrl[2]);\n"
              "endmodule\n"));
}

TEST(ParserA303, EnableTerminal_PassEnableSwitch) {
  // enable_terminal in pass enable switch context
  auto r = Parse(
      "module m;\n"
      "  tranif1 (a, b, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA303, EnableTerminal_PassEnableExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rtranif0 (a, b, x ^ y);\n"
              "endmodule\n"));
}

TEST(ParserA303, InoutTerminal_BitSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  tran (a[0], b[1]);\n"
              "endmodule\n"));
}

TEST(ParserA303, InoutTerminal_PartSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rtran (bus[3:0], net[7:4]);\n"
              "endmodule\n"));
}

}  // namespace
