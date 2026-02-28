// Annex A.4.2: Generated instantiation

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- genvar_initialization: with inline genvar keyword ---
TEST(ParserAnnexA042, GenvarInitWithGenvarKeyword) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i = i + 1) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen->gen_init, nullptr);
}

// --- genvar_iteration: compound assignment_operator (i += 1) ---
TEST(ParserAnnexA042, GenvarIterationCompoundAssign) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i += 1) begin\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_NE(gen->gen_step, nullptr);
}

// --- case_generate_item: default ---
TEST(ParserAnnexA042, CaseGenerateWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    8: assign out = in8;\n"
      "    default: assign out = in_def;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->gen_case_items.size(), 2u);
  EXPECT_FALSE(gen->gen_case_items[0].is_default);
  EXPECT_TRUE(gen->gen_case_items[1].is_default);
}

// --- generate_item: module_or_generate_item (always block) ---
TEST(ParserAnnexA042, GenerateItemAlwaysBlock) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : blk\n"
      "    always @(posedge clk) q[i] <= d[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kAlwaysBlock);
}

}  // namespace
