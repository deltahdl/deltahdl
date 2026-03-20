// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(GateInstantiationPreprocessor, GateInsideConditionalCompilation) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b, y;\n"
      "`ifdef INCLUDE_GATE\n"
      "  and g1(y, a, b);\n"
      "`endif\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd), nullptr);
}

TEST(GateInstantiationPreprocessor, GateWithStrengthAndDelayThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (strong0, strong1) #10 g1(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);
  EXPECT_EQ(g->drive_strength1, 4u);
  EXPECT_NE(g->gate_delay, nullptr);
}

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
