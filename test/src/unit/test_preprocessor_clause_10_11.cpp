#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(NetAliasingPreprocessor, NetAlias) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b, c;\n"
      "  alias a = b = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;

  auto* alias_item = items.back();
  EXPECT_EQ(alias_item->kind, ModuleItemKind::kAlias);
  EXPECT_EQ(alias_item->alias_nets.size(), 3u);
}

TEST(NetAliasingPreprocessor, NetAliasTwoNets) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b;\n"
      "  alias a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  auto* mod = r.cu->modules[0];

  ModuleItem* alias_item = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kAlias) {
      alias_item = item;
      break;
    }
  }
  ASSERT_NE(alias_item, nullptr);
  ASSERT_EQ(alias_item->alias_nets.size(), 2u);
}

TEST(NetAliasingPreprocessor, NetAliasThreeNets) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b, c;\n"
      "  alias a = b = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* alias_item = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kAlias) {
      alias_item = item;
      break;
    }
  }
  ASSERT_NE(alias_item, nullptr);
  ASSERT_EQ(alias_item->alias_nets.size(), 3u);
}

TEST(NetAliasingPreprocessor, MacroExpandedNetNames) {
  auto r = ParseWithPreprocessor(
      "`define SIG_A a\n"
      "`define SIG_B b\n"
      "module m;\n"
      "  wire a, b;\n"
      "  alias `SIG_A = `SIG_B;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetAliasingPreprocessor, ConditionalCompilationAroundAlias) {
  auto r = ParseWithPreprocessor(
      "`define USE_ALIAS\n"
      "module m;\n"
      "  wire a, b;\n"
      "`ifdef USE_ALIAS\n"
      "  alias a = b;\n"
      "`endif\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlias) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(NetAliasingPreprocessor, ConditionalCompilationExcludesAlias) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b;\n"
      "`ifdef UNDEFINED_MACRO\n"
      "  alias a = b;\n"
      "`endif\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlias) found = true;
  }
  EXPECT_FALSE(found);
}

}  // namespace
