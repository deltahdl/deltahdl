// Non-LRM tests

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

TEST(ParserSection27, GenerateRegionWithMultipleKinds) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    for (genvar i = 0; i < 2; i++) begin\n"
      "      assign a[i] = b[i];\n"
      "    end\n"
      "    if (WIDTH > 0)\n"
      "      assign c = d;\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  bool found_for = false;
  bool found_if = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) found_for = true;
    if (item->kind == ModuleItemKind::kGenerateIf) found_if = true;
  }
  EXPECT_TRUE(found_for);
  EXPECT_TRUE(found_if);
}

// --- Loop generate with module instantiation (§27.4) ---
TEST(ParserSection27, GenerateForWithModuleInst) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : blk\n"
      "    sub u(.a(in[i]), .b(out[i]));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kModuleInst);
}

TEST(ParserSection27, GenerateForNestedBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 2; i++) begin : outer\n"
      "    for (genvar j = 0; j < 2; j++) begin : inner\n"
      "      assign out[i][j] = in[i][j];\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* outer = r.cu->modules[0]->items[0];
  EXPECT_EQ(outer->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(outer->gen_body.size(), 1u);
  EXPECT_EQ(outer->gen_body[0]->kind, ModuleItemKind::kGenerateFor);
}

TEST(ParserSection27, GenerateForPreDecrement) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 3; i >= 0; i--) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen->gen_step, nullptr);
}

}  // namespace
