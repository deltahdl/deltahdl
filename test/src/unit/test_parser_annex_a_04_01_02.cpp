// Annex A.4.1.2: Interface instantiation

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- interface_instantiation: multiple hierarchical_instance ---
TEST(ParserAnnexA0412, MultipleInterfaceInstances) {
  auto r = Parse("module m; my_if u0(.a(a)), u1(.a(b)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->inst_module, "my_if");
  EXPECT_EQ(i0->inst_name, "u0");
  EXPECT_EQ(i1->inst_module, "my_if");
  EXPECT_EQ(i1->inst_name, "u1");
}

// --- interface_instantiation: empty port list ---
TEST(ParserAnnexA0412, InterfaceInstEmptyPorts) {
  auto r = Parse("module m; my_if u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_ports.empty());
}

// --- interface_instantiation: interface instantiated inside interface ---
TEST(ParserAnnexA0412, InterfaceInstInsideInterface) {
  auto r = Parse(
      "interface outer_if;\n"
      "  inner_if u0(.clk(clk));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_GE(r.cu->interfaces[0]->items.size(), 1u);
  auto* item = r.cu->interfaces[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "inner_if");
  EXPECT_EQ(item->inst_name, "u0");
}

}  // namespace
