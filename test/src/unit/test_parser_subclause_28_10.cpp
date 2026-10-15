

#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "model_gate_logic.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(PullSources, EmptyTerminals) {
  auto r = Parse(
      "module m;\n"
      "  pullup ();\n"
      "endmodule\n");
  // The terminal list is parsed as an expression list, so the empty one is
  // rejected by Parser::ParsePrimaryExpr under §11.2 rather than by §28.10.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
}

TEST(PullSources, PullupAndPulldownInstantiation) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire net1;\n"
      "  pullup (net1);\n"
      "  pulldown (net1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown),
            nullptr);
}

TEST(PullSources, PullupGateKindAndSingleTerminal) {
  auto r = ParseWithPreprocessor("module t; pullup (o); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kPullup);
  EXPECT_EQ(item->gate_terminals.size(), 1);
}

TEST(PullSources, PulldownGateKindAndSingleTerminal) {
  auto r = ParseWithPreprocessor("module t; pulldown (o); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kPulldown);
  EXPECT_EQ(item->gate_terminals.size(), 1);
}

TEST(PullSources, PullupRejectsDelay) {
  auto r = Parse(
      "module m;\n"
      "  pullup #5 pu1(net1);\n"
      "endmodule\n");
  // §28.3.3 owns the rule that a pull gate takes no delay; §28.10 only defines
  // the two pull sources.
  EXPECT_TRUE(ReportedError(r.diags, "delay not allowed on this gate type", 2,
                            "28.3.3"));
}

TEST(PullSources, PulldownRejectsDelay) {
  auto r = Parse(
      "module m;\n"
      "  pulldown #5 pd1(net1);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "delay not allowed on this gate type", 2,
                            "28.3.3"));
}

// §28.3.2 lets a pull gate carry one strength keyword of the side it drives,
// or a pair of one strength0 and one strength1 keyword in either order; a pair
// of two keywords of one side is neither. Read as the first keyword and a
// second of the wrong side, which the parser recorded as none, both
// declarations below were accepted with the second keyword dropped.
TEST(PullSources, AStrengthPairOfOneSideIsReported) {
  auto r = Parse(
      "module m;\n"
      "  wire o1, o2;\n"
      "  pullup (strong1, strong1) p(o1);\n"
      "  pulldown (pull0, weak0) q(o2);\n"
      "endmodule\n");
  for (uint32_t line : {3u, 4u}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "a pull gate's strength pair is one strength0 "
                              "keyword and one strength1 keyword",
                              line, "28.3.2"))
        << line;
  }
}

// The forms §28.3.2 does give a pull gate stay legal: its own side's keyword
// alone, and a pair of one keyword of each side in either order.
TEST(PullSources, APullGatesOwnKeywordOrAMixedPairIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  wire o1, o2, o3, o4;\n"
      "  pullup (strong1) p1(o1);\n"
      "  pullup (strong1, weak0) p2(o2);\n"
      "  pulldown (weak1, pull0) p3(o3);\n"
      "  pulldown (pull0) p4(o4);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
