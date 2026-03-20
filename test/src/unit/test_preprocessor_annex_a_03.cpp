// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(GateInstantiationPreprocessor, MultipleInstancesThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b, y1, y2;\n"
      "  nand n1(y1, a, b), n2(y2, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
  for (auto* g : gates) {
    EXPECT_EQ(g->gate_kind, GateKind::kNand);
  }
}

}  // namespace
