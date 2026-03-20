// §28.5

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(BufNotGates, SingleTerminal) {
  auto r = Parse(
      "module m;\n"
      "  buf b1(out);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(BufNotGates, MinimumTwoTerminals) {
  auto r = Parse(
      "module m;\n"
      "  not (out, in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNot);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

}  // namespace
