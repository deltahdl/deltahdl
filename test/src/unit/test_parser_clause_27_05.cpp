// §27.5: Conditional generate constructs

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A4GenerateIfElse) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH > 8) begin\n"
      "    wire [15:0] bus;\n"
      "  end else begin\n"
      "    wire [7:0] bus;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) {
      found = true;
      EXPECT_NE(item->gen_else, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParserAnnexA, A4GenerateCase) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    8: begin\n"
      "      wire [7:0] d;\n"
      "    end\n"
      "    default: begin\n"
      "      wire [31:0] d;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateCase);
  EXPECT_EQ(item->gen_case_items.size(), 2u);
}

// --- if_generate_construct: basic if ---
TEST(ParserAnnexA042, IfGenerateBasic) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH > 1)\n"
      "    assign out = in;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_else, nullptr);
}

// --- if_generate_construct: if with else ---
TEST(ParserAnnexA042, IfGenerateWithElse) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH > 1)\n"
      "    assign out = a;\n"
      "  else\n"
      "    assign out = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_NE(gen->gen_else, nullptr);
  ASSERT_EQ(gen->gen_else->gen_body.size(), 1u);
}

// --- if_generate_construct: if / else-if / else chain ---
TEST(ParserAnnexA042, IfGenerateElseIfChain) {
  auto r = Parse(
      "module m;\n"
      "  if (W == 1)\n"
      "    assign out = a;\n"
      "  else if (W == 2)\n"
      "    assign out = b;\n"
      "  else\n"
      "    assign out = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_NE(gen->gen_else, nullptr);
  EXPECT_EQ(gen->gen_else->kind, ModuleItemKind::kGenerateIf);
  ASSERT_NE(gen->gen_else->gen_else, nullptr);
}

// --- case_generate_construct: basic case ---
TEST(ParserAnnexA042, CaseGenerateBasic) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    8: assign out = in8;\n"
      "    16: assign out = in16;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateCase);
  ASSERT_EQ(gen->gen_case_items.size(), 2u);
  EXPECT_FALSE(gen->gen_case_items[0].is_default);
  EXPECT_FALSE(gen->gen_case_items[1].is_default);
}

// --- case_generate_item: multiple patterns ---
TEST(ParserAnnexA042, CaseGenerateMultiplePatterns) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    8, 16: assign out = narrow;\n"
      "    32, 64: assign out = wide;\n"
      "    default: assign out = other;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->gen_case_items.size(), 3u);
  EXPECT_EQ(gen->gen_case_items[0].patterns.size(), 2u);
  EXPECT_EQ(gen->gen_case_items[1].patterns.size(), 2u);
  EXPECT_TRUE(gen->gen_case_items[2].is_default);
}

// --- nested generate constructs: for inside if ---
TEST(ParserAnnexA042, NestedForInsideIf) {
  auto r = Parse(
      "module m;\n"
      "  if (USE_PIPELINE) begin\n"
      "    for (genvar i = 0; i < STAGES; i++) begin : stage\n"
      "      assign pipe[i] = data[i];\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_GE(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kGenerateFor);
}

// §27.1: Generate-if with nested generate-for (hierarchical conditional).
TEST(ParserSection27, GenerateIfWithNestedFor) {
  auto r = Parse(
      "module m;\n"
      "  if (USE_PIPELINE) begin\n"
      "    for (genvar i = 0; i < STAGES; i++) begin : stage\n"
      "      assign pipe[i] = data[i];\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateIf);
  ASSERT_GE(mod->items[0]->gen_body.size(), 1u);
  EXPECT_EQ(mod->items[0]->gen_body[0]->kind, ModuleItemKind::kGenerateFor);
}

using ProgramParseTest = ProgramTestParse;

TEST(ParserSection23, GenerateRegionWithIf) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    if (WIDTH > 8) begin : wide\n"
      "      assign a = b;\n"
      "    end else begin : narrow\n"
      "      assign a = c;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) found = true;
  }
  EXPECT_TRUE(found);
}

// =========================================================================
// LRM section 27.5: Conditional generates (if-generate)
// =========================================================================
TEST(ParserSection23, IfGenerateWithElseIf) {
  auto r = Parse(
      "module m;\n"
      "  if (W == 8) begin : w8\n"
      "    assign a = b;\n"
      "  end else if (W == 16) begin : w16\n"
      "    assign a = c;\n"
      "  end else begin : wother\n"
      "    assign a = d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(item->gen_cond, nullptr);
  EXPECT_FALSE(item->gen_body.empty());
  ASSERT_NE(item->gen_else, nullptr);
  EXPECT_NE(item->gen_else->gen_cond, nullptr);
  ASSERT_NE(item->gen_else->gen_else, nullptr);
}

TEST(ParserSection23, IfGenerateNoElse) {
  auto r = Parse(
      "module m;\n"
      "  if (EN) begin\n"
      "    assign out = in;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(item->gen_cond, nullptr);
  EXPECT_EQ(item->gen_else, nullptr);
}

TEST(ParserSection23, IfGenerateSingleItemNoBegin) {
  auto r = Parse(
      "module m;\n"
      "  if (EN)\n"
      "    assign out = in;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateIf);
  EXPECT_EQ(item->gen_body.size(), 1);
}

TEST(Parser, GenerateIf) {
  auto r = Parse(
      "module t;\n"
      "  if (WIDTH > 8) begin\n"
      "    assign a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(mod->items[0]->gen_cond, nullptr);
  EXPECT_FALSE(mod->items[0]->gen_body.empty());
}

TEST(Parser, GenerateIfElse) {
  auto r = Parse(
      "module t;\n"
      "  if (WIDTH > 8) begin\n"
      "    assign a = b;\n"
      "  end else begin\n"
      "    assign a = c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(item->gen_else, nullptr);
}

static void VerifyGenerateCaseItem(const GenerateCaseItem& ci, size_t idx,
                                   bool expect_default,
                                   size_t expect_pattern_count) {
  EXPECT_EQ(ci.is_default, expect_default) << "case item " << idx;
  EXPECT_EQ(ci.patterns.size(), expect_pattern_count) << "case item " << idx;
  EXPECT_FALSE(ci.body.empty()) << "case item " << idx;
}

TEST(Parser, GenerateCase) {
  auto r = Parse(
      "module t;\n"
      "  case (WIDTH)\n"
      "    1: begin\n"
      "      assign a = b;\n"
      "    end\n"
      "    2: begin\n"
      "      assign a = c;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateCase);
  EXPECT_NE(item->gen_cond, nullptr);
  ASSERT_EQ(item->gen_case_items.size(), 2);
  VerifyGenerateCaseItem(item->gen_case_items[0], 0, false, 1);
  VerifyGenerateCaseItem(item->gen_case_items[1], 1, false, 1);
}

TEST(Parser, GenerateCaseDefault) {
  auto r = Parse(
      "module t;\n"
      "  case (WIDTH)\n"
      "    1: begin\n"
      "      assign a = b;\n"
      "    end\n"
      "    default: begin\n"
      "      assign a = c;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->gen_case_items.size(), 2);
  EXPECT_TRUE(item->gen_case_items[1].is_default);
}

TEST(Parser, GenerateCaseMultiPattern) {
  auto r = Parse(
      "module t;\n"
      "  case (WIDTH)\n"
      "    1, 2: begin\n"
      "      assign a = b;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->gen_case_items.size(), 1);
  EXPECT_EQ(item->gen_case_items[0].patterns.size(), 2);
}

TEST(Parser, GenerateCaseInRegion) {
  auto r = Parse(
      "module t;\n"
      "  generate\n"
      "    case (WIDTH)\n"
      "      1: begin\n"
      "        assign a = b;\n"
      "      end\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateCase) {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// 15. Labeled generate blocks (if-generate)
TEST(ParserClause03, Cl3_13_LabeledIfGenerateBlock) {
  auto r = Parse(
      "module m;\n"
      "  parameter USE_FAST = 1;\n"
      "  if (USE_FAST) begin : fast_path\n"
      "    logic [7:0] result;\n"
      "  end else begin : slow_path\n"
      "    logic [15:0] result;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  bool found_gen_if = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) {
      found_gen_if = true;
      EXPECT_FALSE(item->gen_body.empty());
    }
  }
  EXPECT_TRUE(found_gen_if);
}

TEST(ParserSection23, CaseGenerateMultipleLabels) {
  auto r = Parse(
      "module m;\n"
      "  case (SEL)\n"
      "    0, 1: assign a = b;\n"
      "    2, 3: assign a = c;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateCase);
  ASSERT_EQ(item->gen_case_items.size(), 2);
  EXPECT_EQ(item->gen_case_items[0].patterns.size(), 2);
  EXPECT_EQ(item->gen_case_items[1].patterns.size(), 2);
}

// --- Single-item generate-if without begin/end (§27.5) ---
TEST(ParserSection27, GenerateIfSingleItemParse) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH > 1)\n"
      "    assign out = in;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_EQ(gen->gen_body.size(), 1);
}

TEST(ParserSection27, GenerateIfSingleItemBody) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH > 1)\n"
      "    assign out = in;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kContAssign);
  EXPECT_EQ(gen->gen_else, nullptr);
}

TEST(ParserSection27, GenerateIfElseSingleItemParse) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH > 1)\n"
      "    assign out = a;\n"
      "  else\n"
      "    assign out = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_EQ(gen->gen_body.size(), 1);
}

TEST(ParserSection27, GenerateIfElseSingleItemBranches) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH > 1)\n"
      "    assign out = a;\n"
      "  else\n"
      "    assign out = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kContAssign);
  ASSERT_NE(gen->gen_else, nullptr);
  ASSERT_EQ(gen->gen_else->gen_body.size(), 1);
  EXPECT_EQ(gen->gen_else->gen_body[0]->kind, ModuleItemKind::kContAssign);
}

}  // namespace
