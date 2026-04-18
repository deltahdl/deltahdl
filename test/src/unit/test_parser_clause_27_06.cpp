#include "fixture_parser.h"

using namespace delta;

namespace {

// §27.6: an explicit label preceding a generate block (label : begin ... end)
// is the block's external name.  The parser must retain that identifier on
// the generate ModuleItem so elaboration can honor it instead of assigning a
// default genblk<n>.
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

// §27.6: the alternative form places the label after `begin`
// (begin : name ... end).  Both forms identify the block externally and the
// parser must capture the identifier identically.
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

// §27.6: labels are meaningful for any generate construct, including
// for-generate.  The surviving name becomes the root of the per-iteration
// hierarchical path.
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

// §27.6: an unnamed generate block carries no user-supplied label out of the
// parser; the default genblk<n> name is assigned later during elaboration.
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

}  // namespace
