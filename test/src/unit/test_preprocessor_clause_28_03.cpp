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

// --- Drive strength in gate instantiation context ---
TEST(ParserA222, DriveStrengthGateInst) {
  // drive_strength used with gate instantiation
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and (supply0, supply1) g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // wire y, a, b creates 3 items; gate is at index 3
  auto* item = r.cu->modules[0]->items[3];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->drive_strength0, 5u);  // supply0 = 5
  EXPECT_EQ(item->drive_strength1, 5u);  // supply1 = 5
}

static void VerifyGateInstances(const std::vector<ModuleItem*>& items,
                                GateKind kind,
                                const std::string expected_names[],
                                size_t count) {
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(items[i]->gate_kind, kind);
    EXPECT_EQ(items[i]->gate_inst_name, expected_names[i]);
    EXPECT_EQ(items[i]->gate_terminals.size(), 3);
  }
}

TEST(ParserSection28, MultipleInstances) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  and g1(a, b, c), g2(d, e, f);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  std::string expected_names[] = {"g1", "g2"};
  VerifyGateInstances(mod->items, GateKind::kAnd, expected_names, 2);
}

TEST(ParserSection28, MultipleInstancesThree) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  nand n1(a, b, c), n2(d, e, f), n3(g, h, i);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 3);
  EXPECT_EQ(mod->items[0]->gate_inst_name, "n1");
  EXPECT_EQ(mod->items[1]->gate_inst_name, "n2");
  EXPECT_EQ(mod->items[2]->gate_inst_name, "n3");
}

TEST(ParserSection28, MultipleInstancesNoNames) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  or (a, b, c), (d, e, f);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  EXPECT_TRUE(mod->items[0]->gate_inst_name.empty());
  EXPECT_TRUE(mod->items[1]->gate_inst_name.empty());
}

}  // namespace
