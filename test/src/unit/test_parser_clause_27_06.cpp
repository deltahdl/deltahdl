#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(GenerateBlockNaming, PrefixLabelRetainedOnGenerateIf) {
  auto r = Parse(
      "module m;\n"
      "  if (1) g1 : begin\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateIf);
  EXPECT_EQ(mod->items[0]->name, "g1");
}

TEST(GenerateBlockNaming, SuffixLabelRetainedOnGenerateIf) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin : g1\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateIf);
  EXPECT_EQ(mod->items[0]->name, "g1");
}

TEST(GenerateBlockNaming, SuffixLabelRetainedOnGenerateFor) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin : bitnum\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* loop = nullptr;
  for (auto* it : mod->items) {
    if (it->kind == ModuleItemKind::kGenerateFor) loop = it;
  }
  ASSERT_NE(loop, nullptr);
  EXPECT_EQ(loop->name, "bitnum");
}

TEST(GenerateBlockNaming, UnnamedBlockHasNoParserLabel) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateIf);
  EXPECT_TRUE(mod->items[0]->name.empty());
}

}
