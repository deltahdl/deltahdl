// §28.3.5: The range specification

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection28, GateArrayRange) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  nand n[0:3](out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kNand);
}

TEST(ParserSection28, GateArrayWithDelay) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  and #5 g[0:7](out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_NE(item->gate_delay, nullptr);
}

}  // namespace
