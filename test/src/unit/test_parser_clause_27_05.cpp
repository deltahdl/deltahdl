#include "fixture_parser.h"

using namespace delta;

namespace {

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
  EXPECT_EQ(tail->gen_cond, nullptr);
}

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

TEST(ConditionalGenerateParsing, DanglingElseBindsToNearestIf) {
  // §27.5: when one if-generate is nested directly inside another, a trailing
  // else attaches to the nearest (inner) if, not the outer one.
  auto r = Parse(
      "module m;\n"
      "  if (1)\n"
      "    if (0) begin\n"
      "      logic a;\n"
      "    end else begin\n"
      "      logic b;\n"
      "    end\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto* outer = mod->items[0];
  EXPECT_EQ(outer->kind, ModuleItemKind::kGenerateIf);
  // The else was consumed by the inner if, so the outer if has none.
  EXPECT_EQ(outer->gen_else, nullptr);
  ASSERT_EQ(outer->gen_body.size(), 1u);
  auto* inner = outer->gen_body[0];
  EXPECT_EQ(inner->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(inner->gen_else, nullptr);
}

TEST(ConditionalGenerateParsing, CombineIfAndCaseGenerate) {
  // §27.5: an if-generate and a case-generate may be combined in one scheme;
  // here the else alternative of an if-generate is itself a case-generate.
  auto r = Parse(
      "module m #(parameter SEL = 0) ();\n"
      "  if (SEL == 0) begin\n"
      "    logic a;\n"
      "  end else case (SEL)\n"
      "    1: begin logic b; end\n"
      "    default: begin logic c; end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto* outer = mod->items[0];
  EXPECT_EQ(outer->kind, ModuleItemKind::kGenerateIf);
  ASSERT_NE(outer->gen_else, nullptr);
  ASSERT_GE(outer->gen_else->gen_body.size(), 1u);
  EXPECT_EQ(outer->gen_else->gen_body[0]->kind, ModuleItemKind::kGenerateCase);
}

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
