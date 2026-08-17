#include "fixture_parser.h"

using namespace delta;

namespace {

// A module whose only item is the generate construct written in `body`, so a
// pair of cases differing only in whether a block carries `begin` and `end`
// can be written that way. The two parameters stand in the header because a
// case generate needs an expression to select on and a declaration in the body
// would leave the module holding more than the construct under test.
std::string ModuleAround(const std::string& body) {
  return "module m #(parameter SEL = 0, parameter q = 0) ();\n" + body +
         "endmodule\n";
}

// The construct ModuleAround wrapped, or nullptr when the parse left something
// else there. Reaching it here leaves each case below with the source it parses
// and the one field it reads.
ModuleItem* SoleGenerateItem(ParseResult& r, ModuleItemKind kind) {
  if (r.cu == nullptr || r.cu->modules.empty()) return nullptr;
  const auto& items = r.cu->modules[0]->items;
  if (items.size() != 1 || items[0]->kind != kind) return nullptr;
  return items[0];
}

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

// The six cases below come in three pairs, one pair per position A.4.2 writes
// a generate_block in a conditional generate construct. Each pair holds the
// source fixed and varies only the `begin` and `end` keywords, because a case
// written for the begin-end source alone is satisfied by a field that is
// always true.
TEST(ConditionalGenerateParsing, IfThenBlockRecordsBeginEnd) {
  auto r = Parse(ModuleAround("  if (1) begin logic a; end\n"));
  ASSERT_FALSE(r.has_errors);
  auto* item = SoleGenerateItem(r, ModuleItemKind::kGenerateIf);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->gen_body_has_begin_end);
}

TEST(ConditionalGenerateParsing, IfThenSingleItemRecordsNoBeginEnd) {
  auto r = Parse(ModuleAround("  if (1) logic a;\n"));
  ASSERT_FALSE(r.has_errors);
  auto* item = SoleGenerateItem(r, ModuleItemKind::kGenerateIf);
  ASSERT_NE(item, nullptr);
  EXPECT_FALSE(item->gen_body_has_begin_end);
}

TEST(ConditionalGenerateParsing, ElseBlockRecordsBeginEnd) {
  // The else branch of an if generate construct is held in a second item,
  // reached through gen_else, whose own gen_body_has_begin_end describes the
  // block written after `else`.
  auto r =
      Parse(ModuleAround("  if (1) begin logic a; end\n"
                         "  else begin case (q) 0: logic b; endcase end\n"));
  ASSERT_FALSE(r.has_errors);
  auto* item = SoleGenerateItem(r, ModuleItemKind::kGenerateIf);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->gen_else, nullptr);
  EXPECT_TRUE(item->gen_else->gen_body_has_begin_end);
}

TEST(ConditionalGenerateParsing, ElseSingleItemRecordsNoBeginEnd) {
  // §27.5, printed page 824: a generate block holding only a conditional
  // generate construct without begin and end is not a separate scope, and the
  // construct in it is directly nested. This source and the one above differ
  // only in those two keywords, so this field is all that tells the directly
  // nested case generate from the one written inside a scope of its own.
  auto r =
      Parse(ModuleAround("  if (1) begin logic a; end\n"
                         "  else case (q) 0: logic b; endcase\n"));
  ASSERT_FALSE(r.has_errors);
  auto* item = SoleGenerateItem(r, ModuleItemKind::kGenerateIf);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->gen_else, nullptr);
  EXPECT_FALSE(item->gen_else->gen_body_has_begin_end);
}

TEST(ConditionalGenerateParsing, CaseAlternativeBlockRecordsBeginEnd) {
  auto r =
      Parse(ModuleAround("  case (SEL) 0, 1, 2: begin logic a; end\n"
                         "  endcase\n"));
  ASSERT_FALSE(r.has_errors);
  auto* item = SoleGenerateItem(r, ModuleItemKind::kGenerateCase);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->gen_case_items.size(), 1u);
  EXPECT_TRUE(item->gen_case_items[0].has_begin_end);
}

TEST(ConditionalGenerateParsing, CaseAlternativeSingleItemRecordsNoBeginEnd) {
  auto r =
      Parse(ModuleAround("  case (SEL) 0, 1, 2: logic a;\n"
                         "  endcase\n"));
  ASSERT_FALSE(r.has_errors);
  auto* item = SoleGenerateItem(r, ModuleItemKind::kGenerateCase);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->gen_case_items.size(), 1u);
  EXPECT_FALSE(item->gen_case_items[0].has_begin_end);
}

}  // namespace
