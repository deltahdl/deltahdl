#include "fixture_parser.h"
#include "fixture_program.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DeclarationAssignmentParsing, SpecparamAssignmentMintypmax) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tDelay = 1:2:3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SourceText, SpecparamAsModuleItem) {
  auto r = Parse(
      "module m;\n"
      "  specparam delay = 10;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kSpecparam);
}

TEST(DeclarationAssignmentParsing, SpecparamAssignmentBasic) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tRise = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST_F(SpecifyParseTest, SpecparamDeclaration) {
  auto* unit = Parse("module m; specparam tRISE = 10; endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(items[0]->name, "tRISE");
}

TEST_F(SpecifyParseTest, SpecparamWithRange) {
  auto* unit = Parse("module m; specparam [31:0] tDELAY = 100; endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(items[0]->name, "tDELAY");
}

TEST_F(SpecifyParseTest, MultipleSpecparams) {
  auto* unit =
      Parse("module m; specparam tRISE = 10; specparam tFALL = 12; endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(items[0]->name, "tRISE");
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(items[1]->name, "tFALL");
}

TEST_F(SpecifyTest, SpecparamInsideSpecify) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  specparam tRISE = 10;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kSpecparam);
  EXPECT_EQ(item->param_name, "tRISE");
  EXPECT_NE(item->param_value, nullptr);
}
static bool HasSpecifyItemKind(ModuleItem* spec_block, SpecifyItemKind kind) {
  for (auto* si : spec_block->specify_items) {
    if (si->kind == kind) return true;
  }
  return false;
}

TEST(GateLevelModelingParsing, SpecifyBlockWithSpecparam) {
  auto r = Parse(
      "module m(input clk, output q);\n"
      "  specify\n"
      "    specparam tDelay = 10;\n"
      "    (clk => q) = tDelay;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  EXPECT_TRUE(HasSpecifyItemKind(spec, SpecifyItemKind::kSpecparam));
  EXPECT_TRUE(HasSpecifyItemKind(spec, SpecifyItemKind::kPathDecl));
}

TEST(SpecifyBlockDeclParsing, SpecparamMultipleDecls) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tRISE = 100, tFALL = 200;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SpecifyBlockDeclParsing, SpecifyItemSpecparamDecl) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tPD = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kSpecparam);
}

}  // namespace
