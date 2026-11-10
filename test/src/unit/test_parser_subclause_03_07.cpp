#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"

using namespace delta;

namespace {

std::vector<GateKind> GateKindsOf(const ModuleDecl& m) {
  std::vector<GateKind> kinds;
  for (const auto* item : m.items) {
    if (item->kind == ModuleItemKind::kGateInst)
      kinds.push_back(item->gate_kind);
  }
  return kinds;
}

TEST(PrimitiveBuildingBlock,
     PrimitiveEndprimitiveEnclosesAUserDefinedPrimitive) {
  auto r = Parse(
      "primitive inverter(output o, input i);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive : inverter\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "inverter");
  EXPECT_EQ(r.cu->udps[0]->output_name, "o");
  ASSERT_EQ(r.cu->udps[0]->input_names.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->input_names[0], "i");
}

TEST(PrimitiveBuildingBlock, BuiltInLogicGatesNeedNoDefinition) {
  auto r = Parse(
      "module m(input a, input b, output y1, output y2, output y3);\n"
      "  nand g1(y1, a, b);\n"
      "  xor g2(y2, a, b);\n"
      "  bufif1 g3(y3, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(GateKindsOf(*r.cu->modules[0]),
            (std::vector<GateKind>{GateKind::kNand, GateKind::kXor,
                                   GateKind::kBufif1}));
}

TEST(PrimitiveBuildingBlock, BuiltInSwitchesNeedNoDefinition) {
  auto r = Parse(
      "module m(input g, inout x, inout y, output z);\n"
      "  wire d;\n"
      "  nmos s1(z, d, g);\n"
      "  tran s2(x, y);\n"
      "  pullup p1(d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(GateKindsOf(*r.cu->modules[0]),
            (std::vector<GateKind>{GateKind::kNmos, GateKind::kTran,
                                   GateKind::kPullup}));
}

}  // namespace
