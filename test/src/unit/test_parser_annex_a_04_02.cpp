#include "fixture_parser.h"

using namespace delta;

namespace {

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

TEST(ParserAnnexA042, GenerateItemInInterface) {
  auto r = Parse(
      "interface my_if;\n"
      "  if (W > 0)\n"
      "    wire a;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  bool found_if = false;
  for (auto* item : r.cu->interfaces[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) found_if = true;
  }
  EXPECT_TRUE(found_if);
}

}
