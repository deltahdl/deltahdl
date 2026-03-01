// §28.3: Gate and switch declaration syntax

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

static bool HasGateOfKind(const std::vector<ModuleItem*>& items,
                          GateKind kind) {
  for (const auto* item : items)
    if (item->kind == ModuleItemKind::kGateInst && item->gate_kind == kind)
      return true;
  return false;
}

namespace {

// =============================================================================
// LRM §3.7 — Primitives
// =============================================================================
// §3.7:
//       — logic gates and switches instantiated inside a module.
TEST(ParserClause03, Cl3_7_BuiltInPrimitives) {
  auto r = ParseWithPreprocessor(
      "module gate_test(input a, b, c, output w, x, y, z);\n"
      "  and g1(w, a, b);\n"
      "  nand g2(x, a, b, c);\n"
      "  bufif0 g3(y, a, b);\n"
      "  nmos g4(z, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kGateInst), 4);
  EXPECT_TRUE(HasGateOfKind(r.cu->modules[0]->items, GateKind::kAnd));
  EXPECT_TRUE(HasGateOfKind(r.cu->modules[0]->items, GateKind::kNand));
  EXPECT_TRUE(HasGateOfKind(r.cu->modules[0]->items, GateKind::kBufif0));
  EXPECT_TRUE(HasGateOfKind(r.cu->modules[0]->items, GateKind::kNmos));
}

}  // namespace
