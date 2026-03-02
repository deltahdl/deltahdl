// §28.8: Bidirectional pass switches

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection28, PassGateTran) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  tran (a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kTran);
  ASSERT_EQ(item->gate_terminals.size(), 2);
}

}  // namespace
