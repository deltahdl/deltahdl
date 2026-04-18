#include "fixture_parser.h"

using namespace delta;

namespace {

// §27.5: else attaches to the nearest preceding if, allowing the parser to
// nest a second if-generate as the else branch of the first.
TEST(ConditionalGenerateParsing, IfElseIfChainNests) {
  auto r = Parse(
      "module m;\n"
      "  if (0) begin\n"
      "    logic a;\n"
      "  end else if (1) begin\n"
      "    logic b;\n"
      "  end else begin\n"
      "    logic c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto* outer = mod->items[0];
  EXPECT_EQ(outer->kind, ModuleItemKind::kGenerateIf);
  ASSERT_NE(outer->gen_else, nullptr);
  auto* middle = outer->gen_else;
  EXPECT_EQ(middle->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(middle->gen_cond, nullptr);
  ASSERT_NE(middle->gen_else, nullptr);
  auto* tail = middle->gen_else;
  EXPECT_EQ(tail->gen_cond, nullptr);  // terminal else carries no condition
}

// §27.5: a case-generate item may list several constant expressions separated
// by commas; any match selects that item's generate block.
TEST(ConditionalGenerateParsing, CaseItemWithMultiplePatterns) {
  auto r = Parse(
      "module m #(parameter SEL = 0) ();\n"
      "  case (SEL)\n"
      "    0, 1, 2: begin logic early; end\n"
      "    default: begin logic late; end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto* cg = mod->items[0];
  EXPECT_EQ(cg->kind, ModuleItemKind::kGenerateCase);
  ASSERT_EQ(cg->gen_case_items.size(), 2u);
  EXPECT_EQ(cg->gen_case_items[0].patterns.size(), 3u);
  EXPECT_FALSE(cg->gen_case_items[0].is_default);
  EXPECT_TRUE(cg->gen_case_items[1].is_default);
  EXPECT_EQ(cg->gen_case_items[1].patterns.size(), 0u);
}

// §27.5: the body of a conditional generate construct is a generate_block,
// which may be a single generate_item when no begin/end is used.
TEST(ConditionalGenerateParsing, IfBodyWithoutBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  if (1) logic w;\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto* cg = mod->items[0];
  EXPECT_EQ(cg->kind, ModuleItemKind::kGenerateIf);
  ASSERT_GE(cg->gen_body.size(), 1u);
  EXPECT_EQ(cg->gen_body[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(cg->gen_else, nullptr);
}

}  // namespace
