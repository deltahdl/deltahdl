#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- Req 1: A module can be declared within another module ---

TEST(NestedModuleParsing, NestedModuleDeclaration) {
  auto r = ParseWithPreprocessor(
      "module outer;\n"
      "  module inner;\n"
      "  endmodule\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind,
            ModuleItemKind::kNestedModuleDecl);
  EXPECT_NE(r.cu->modules[0]->items[0]->nested_module_decl, nullptr);
  EXPECT_EQ(r.cu->modules[0]->items[0]->nested_module_decl->name, "inner");
}

TEST(NestedModuleParsing, MultipleNestedModules) {
  auto r = ParseWithPreprocessor(
      "module outer;\n"
      "  module a;\n"
      "  endmodule\n"
      "  module b;\n"
      "  endmodule\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(CountItemsByKind(r.cu->modules[0]->items,
                             ModuleItemKind::kNestedModuleDecl),
            2u);
}

TEST(NestedModuleParsing, NestedInterfaceDeclaration) {
  auto r = ParseWithPreprocessor(
      "module outer;\n"
      "  interface inner_ifc;\n"
      "  endinterface\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind,
            ModuleItemKind::kNestedModuleDecl);
  auto* nested = r.cu->modules[0]->items[0]->nested_module_decl;
  ASSERT_NE(nested, nullptr);
  EXPECT_EQ(nested->decl_kind, ModuleDeclKind::kInterface);
  EXPECT_EQ(nested->name, "inner_ifc");
}

// --- Req 4/5: Port presence distinguishes implicit instantiation ---

TEST(NestedModuleParsing, NestedModuleWithPortsAstStructure) {
  auto r = ParseWithPreprocessor(
      "module outer;\n"
      "  module inner(input a, output b);\n"
      "    assign b = a;\n"
      "  endmodule\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nested = r.cu->modules[0]->items[0]->nested_module_decl;
  ASSERT_NE(nested, nullptr);
  EXPECT_EQ(nested->name, "inner");
  EXPECT_FALSE(nested->ports.empty());
}

TEST(NestedModuleParsing, NestedModulePortlessAstStructure) {
  auto r = ParseWithPreprocessor(
      "module outer;\n"
      "  module inner;\n"
      "    wire w;\n"
      "  endmodule\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nested = r.cu->modules[0]->items[0]->nested_module_decl;
  ASSERT_NE(nested, nullptr);
  EXPECT_EQ(nested->name, "inner");
  EXPECT_TRUE(nested->ports.empty());
}

// --- Macro expansion inside nested modules ---

TEST(NestedModuleParsing, MacroInsideNestedModule) {
  auto r = ParseWithPreprocessor(
      "`define VAL 1'b1\n"
      "module outer;\n"
      "  module inner;\n"
      "    wire w;\n"
      "    assign w = `VAL;\n"
      "  endmodule\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind,
            ModuleItemKind::kNestedModuleDecl);
}

}  // namespace
