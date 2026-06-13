#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(GenerateInstantiationGrammar, GenerateRegionBasic) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire w;\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->modules[0]->items.size(), 1u);
}

TEST(GenerateInstantiationGrammar, GenerateRegionEmpty) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

TEST(GenerateInstantiationGrammar, GenerateRegionMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire a;\n"
      "    wire b;\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(GenerateInstantiationGrammar, GenerateRegionMixedConstructs) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    for (genvar i = 0; i < 2; i++) begin\n"
      "      wire w;\n"
      "    end\n"
      "    if (W > 0)\n"
      "      wire a;\n"
      "    case (SEL)\n"
      "      0: wire x;\n"
      "      default: wire y;\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(HasItemOfKind(mod->items, ModuleItemKind::kGenerateFor));
  EXPECT_TRUE(HasItemOfKind(mod->items, ModuleItemKind::kGenerateIf));
  EXPECT_TRUE(HasItemOfKind(mod->items, ModuleItemKind::kGenerateCase));
}

TEST(GenerateInstantiationGrammar, GenerateRegionWithFor) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < 4; i = i + 1) begin : blk\n"
      "      assign a[i] = b[i];\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(GenerateInstantiationGrammar, GenerateRegionWithIf) {
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

TEST(GenerateInstantiationGrammar, GenvarExprInGenerateFor) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < 4; i = i + 1) begin : gen_blk\n"
      "      wire w;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(GenerateInstantiationGrammar, IntegerTypesInGenerateBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  generate\n"
              "    genvar i;\n"
              "    for (i = 0; i < 4; i = i + 1) begin : gen_blk\n"
              "      int local_count;\n"
              "    end\n"
              "  endgenerate\n"
              "endmodule\n"));
}

TEST(GenerateInstantiationGrammar, LoopGenerateBasic) {
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
  ASSERT_NE(gen->gen_cond, nullptr);
  ASSERT_NE(gen->gen_step, nullptr);
  ASSERT_EQ(gen->gen_body.size(), 1u);
}

TEST(GenerateInstantiationGrammar, LoopGenerateWithPredeclaredGenvar) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(GenerateInstantiationGrammar, LoopGenerateInitCondStep) {
  auto r = Parse(
      "module t;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin\n"
      "    assign a[i] = b[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen, nullptr);
  EXPECT_NE(gen->gen_init, nullptr);
  EXPECT_NE(gen->gen_cond, nullptr);
  EXPECT_NE(gen->gen_step, nullptr);
  EXPECT_FALSE(gen->gen_body.empty());
}

TEST(GenerateInstantiationGrammar, LoopGenerateForStructure) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 8; i = i + 1) begin : bits\n"
      "    assign out[i] = ^in[7:i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = FindItemByKind(r, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen, nullptr);
  EXPECT_NE(gen->gen_init, nullptr);
  EXPECT_NE(gen->gen_cond, nullptr);
  EXPECT_NE(gen->gen_step, nullptr);
  EXPECT_FALSE(gen->gen_body.empty());
}

TEST(GenerateInstantiationGrammar, LoopGenerateInlineGenvar) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i = i + 1) begin : g\n"
      "    assign a[i] = b[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = FindItemByKind(r, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen, nullptr);
  EXPECT_NE(gen->gen_init, nullptr);
}

TEST(GenerateInstantiationGrammar, LoopGenerateWithModuleInst) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : stage\n"
      "    sub u (.a(in[i]), .b(out[i]));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = FindItemByKind(r, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen, nullptr);
  ASSERT_EQ(gen->gen_body.size(), 1);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kModuleInst);
}

TEST(GenerateInstantiationGrammar, GenerateNestedLoops) {
  auto r = Parse(
      "module m;\n"
      "  genvar i, j;\n"
      "  for (i = 0; i < 2; i = i + 1) begin : B1\n"
      "    for (j = 0; j < 2; j = j + 1) begin : B2\n"
      "      assign a[i][j] = b[i][j];\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ModuleItem* outer = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) outer = item;
  }
  ASSERT_NE(outer, nullptr);
  bool has_inner = false;
  for (auto* inner : outer->gen_body) {
    if (inner->kind == ModuleItemKind::kGenerateFor) has_inner = true;
  }
  EXPECT_TRUE(has_inner);
}

TEST(GenerateInstantiationGrammar, GenerateIfInsideForLoop) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : blk\n"
      "    if (i > 0) begin : guard\n"
      "      assign a[i] = b[i-1];\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ModuleItem* gen = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) gen = item;
  }
  ASSERT_NE(gen, nullptr);
  bool has_if = false;
  for (auto* inner : gen->gen_body) {
    if (inner->kind == ModuleItemKind::kGenerateIf) has_if = true;
  }
  EXPECT_TRUE(has_if);
}

TEST(GenerateInstantiationGrammar, NestedForInsideFor) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 2; i++) begin : outer\n"
      "    for (genvar j = 0; j < 2; j++) begin : inner\n"
      "      assign out[i][j] = in[i][j];\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* outer = r.cu->modules[0]->items[0];
  EXPECT_EQ(outer->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(outer->gen_body.size(), 1u);
  EXPECT_EQ(outer->gen_body[0]->kind, ModuleItemKind::kGenerateFor);
}

TEST(GenerateInstantiationGrammar, NestedForInsideIf) {
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

TEST(GenerateInstantiationGrammar, GenvarInitWithGenvarKeyword) {
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

TEST(GenerateInstantiationGrammar, GenvarInitWithoutGenvarKeyword) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(GenerateInstantiationGrammar, GenvarIterationCompoundAssign) {
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

TEST(GenerateInstantiationGrammar, GenvarIterationAssignment) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i = i + 1) begin\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_NE(gen->gen_step, nullptr);
}

TEST(GenerateInstantiationGrammar, GenvarIterationPostIncrement) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_NE(gen->gen_step, nullptr);
}

TEST(GenerateInstantiationGrammar, GenvarExprInLoopBound) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2 * N; i = i + 2) begin : evens\n"
      "    assign a[i] = b[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ModuleItem* gen = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) gen = item;
  }
  ASSERT_NE(gen, nullptr);
  EXPECT_NE(gen->gen_cond, nullptr);
  EXPECT_NE(gen->gen_step, nullptr);
}

TEST(GenerateInstantiationGrammar, IfGenerateBasic) {
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

TEST(GenerateInstantiationGrammar, IfGenerateWithElse) {
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

TEST(GenerateInstantiationGrammar, IfGenerateElseIfChain) {
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

TEST(GenerateInstantiationGrammar, IfGenerateWithElseBeginEnd) {
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

TEST(GenerateInstantiationGrammar, IfGenerateWithElseIf) {
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

TEST(GenerateInstantiationGrammar, IfGenerateNoElse) {
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

TEST(GenerateInstantiationGrammar, IfGenerateSingleItemNoBegin) {
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

TEST(GenerateInstantiationGrammar, ConditionalGenerateIfElse) {
  auto r = Parse(
      "module top;\n"
      "  if (WIDTH == 8) begin\n"
      "    assign out = a;\n"
      "  end else begin\n"
      "    assign out = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_NE(gen->gen_else, nullptr);
}

TEST(GenerateInstantiationGrammar, IfGenerateConditionAndBody) {
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

TEST(GenerateInstantiationGrammar, GenerateIfElse) {
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

TEST(GenerateInstantiationGrammar, LabeledIfGenerateBlock) {
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

TEST(GenerateInstantiationGrammar, IfGenerateNamedBlockWithWire) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter int P = 1;\n"
              "  if (P) begin : gen\n"
              "    wire w;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(GenerateInstantiationGrammar, CaseGenerateBasic) {
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

TEST(GenerateInstantiationGrammar, CaseGenerateWithDefault) {
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

TEST(GenerateInstantiationGrammar, CaseGenerateMultiplePatterns) {
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

TEST(GenerateInstantiationGrammar, CaseGenerateWithBeginEnd) {
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

TEST(GenerateInstantiationGrammar, CaseGenerateMultipleLabels) {
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

TEST(GenerateInstantiationGrammar, ConditionalGenerateCase) {
  auto r = Parse(
      "module top;\n"
      "  case (MODE)\n"
      "    0: assign out = a;\n"
      "    1: assign out = b;\n"
      "    default: assign out = 0;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateCase);
  ASSERT_EQ(gen->gen_case_items.size(), 3u);
}

static void VerifyGenerateCaseItem(const GenerateCaseItem& ci, size_t idx,
                                   bool expect_default,
                                   size_t expect_pattern_count) {
  EXPECT_EQ(ci.is_default, expect_default) << "case item " << idx;
  EXPECT_EQ(ci.patterns.size(), expect_pattern_count) << "case item " << idx;
  EXPECT_FALSE(ci.body.empty()) << "case item " << idx;
}

TEST(GenerateInstantiationGrammar, CaseGenerateTwoItems) {
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

TEST(GenerateInstantiationGrammar, GenerateCaseDefault) {
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

TEST(GenerateInstantiationGrammar, GenerateCaseMultiPattern) {
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

TEST(GenerateInstantiationGrammar, GenerateCaseInRegion) {
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

TEST(GenerateInstantiationGrammar, GenerateBlockLabeled) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : gen_blk\n"
      "    assign out[i] = in[i];\n"
      "  end : gen_blk\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1u);
}

TEST(GenerateInstantiationGrammar, GenerateBlockMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  if (W > 0) begin\n"
      "    wire a;\n"
      "    assign a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  EXPECT_GE(gen->gen_body.size(), 2u);
}

TEST(GenerateInstantiationGrammar, GenerateBlockSingleItem) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++)\n"
      "    assign out[i] = in[i];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kContAssign);
}

TEST(GenerateInstantiationGrammar, GenerateBlockNamedBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : gen_blk\n"
      "    wire w;\n"
      "    assign w = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) {
      found = true;
      EXPECT_FALSE(item->gen_body.empty());
    }
  }
  EXPECT_TRUE(found);
}

TEST(GenerateInstantiationGrammar, IndexedGenerateBlockName) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : stage\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ModuleItem* gen = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) gen = item;
  }
  ASSERT_NE(gen, nullptr);
  EXPECT_FALSE(gen->gen_body.empty());
}

TEST(GenerateInstantiationGrammar, EndLabelOnGenerateBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  genvar i;\n"
              "  for (i = 0; i < 4; i = i + 1) begin : blk\n"
              "    assign a[i] = b[i];\n"
              "  end : blk\n"
              "endmodule\n"));
}

TEST(GenerateInstantiationGrammar, GenerateBlockInRegionWithParameter) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter N = 4) ();\n"
              "  genvar i;\n"
              "  generate\n"
              "    for (i = 0; i < N; i = i + 1) begin : gen_loop\n"
              "      logic [7:0] data;\n"
              "    end\n"
              "  endgenerate\n"
              "endmodule\n"));
}

TEST(GenerateInstantiationGrammar, GenerateForBlockScope) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : gen_blk\n"
      "    logic [7:0] data;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  bool found_gen = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) {
      found_gen = true;
      EXPECT_FALSE(item->gen_body.empty());
    }
  }
  EXPECT_TRUE(found_gen);
}

TEST(GenerateInstantiationGrammar, ForGenerateNamedBlockWithWire) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  genvar i;\n"
              "  for (i = 0; i < 4; i = i + 1) begin : gen\n"
              "    wire w;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(GenerateInstantiationGrammar, GenerateItemAlwaysBlock) {
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

TEST(GenerateInstantiationGrammar, GenerateItemModuleInst) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : blk\n"
      "    sub u(.a(in[i]), .b(out[i]));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kModuleInst);
}

TEST(GenerateInstantiationGrammar, GenerateItemInInterface) {
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

TEST(GenerateInstantiationGrammar, GenerateForInstantiation) {
  auto r = Parse(
      "module top;\n"
      "  for (genvar i = 0; i < 4; i++) begin : gen_blk\n"
      "    sub u(.a(w[i]));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(mod->items[0]->gen_body.size(), 1u);
  EXPECT_EQ(mod->items[0]->gen_body[0]->kind, ModuleItemKind::kModuleInst);
}

TEST(GenerateInstantiationGrammar, GenvarIterationPreIncrement) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; ++i) begin\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen->gen_step, nullptr);
}

TEST(GenerateInstantiationGrammar, GenvarInitNonZeroStart) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 3; i >= 0; i--) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu->modules[0]->items[0]->gen_init, nullptr);
}

TEST(GenerateInstantiationGrammar, GenvarInitConstantExpression) {
  auto r = Parse(
      "module m #(parameter N = 4) ();\n"
      "  for (genvar i = N - 1; i >= 0; i--) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu->modules[0]->items[0]->gen_init, nullptr);
}

TEST(GenerateInstantiationGrammar, CaseGenerateDefaultNoColon) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    8: assign out = in8;\n"
      "    default assign out = in_def;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->gen_case_items.size(), 2u);
  EXPECT_TRUE(gen->gen_case_items[1].is_default);
}

TEST(GenerateInstantiationGrammar, GenerateBlockEmptyBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  if (EN) begin\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  EXPECT_TRUE(gen->gen_body.empty());
}

TEST(GenerateInstantiationGrammar, GenerateForEmptyBody) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  EXPECT_TRUE(gen->gen_body.empty());
}

TEST(GenerateInstantiationGrammar, CaseGenerateEmptyItem) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    8: begin end\n"
      "    default: begin end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateCase);
  ASSERT_EQ(gen->gen_case_items.size(), 2u);
  EXPECT_TRUE(gen->gen_case_items[0].body.empty());
  EXPECT_TRUE(gen->gen_case_items[1].body.empty());
}

TEST(GenerateInstantiationGrammar, GenerateBlockLabelBeginOnly) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  for (genvar i = 0; i < 4; i++) begin : blk\n"
              "    wire w;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(GenerateInstantiationGrammar, GenerateBlockLabelAfterBegin) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  for (genvar i = 0; i < 4; i++) begin : blk\n"
              "    wire w;\n"
              "  end : blk\n"
              "endmodule\n"));
}

TEST(GenerateInstantiationGrammar, NestedGenerateRegion) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    generate\n"
      "      wire a;\n"
      "    endgenerate\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 1u);
}

TEST(GenerateInstantiationGrammar, GenerateIfInChecker) {
  auto r = Parse(
      "checker my_chk;\n"
      "  if (1) begin\n"
      "    wire w;\n"
      "  end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(GenerateInstantiationGrammar, GenerateForInChecker) {
  auto r = Parse(
      "checker my_chk;\n"
      "  for (genvar i = 0; i < 4; i++) begin\n"
      "    wire w;\n"
      "  end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(GenerateInstantiationGrammar, GenerateItemWithParamDecl) {
  auto r = Parse(
      "module m;\n"
      "  if (W > 0) begin : blk\n"
      "    localparam int X = 5;\n"
      "    wire [X-1:0] data;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  EXPECT_GE(gen->gen_body.size(), 2u);
}

TEST(GenerateInstantiationGrammar, GenerateItemWithInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  if (SIM) begin\n"
      "    initial $display(\"sim\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_GE(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kInitialBlock);
}

TEST(GenerateInstantiationGrammar, GenerateItemWithFunction) {
  auto r = Parse(
      "module m;\n"
      "  if (EN) begin : blk\n"
      "    function automatic int add(int a, int b);\n"
      "      return a + b;\n"
      "    endfunction\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(GenerateInstantiationGrammar, CaseGenerateSingleItem) {
  auto r = Parse(
      "module m;\n"
      "  case (MODE)\n"
      "    0: assign out = in;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateCase);
  ASSERT_EQ(gen->gen_case_items.size(), 1u);
}

TEST(GenerateInstantiationGrammar, CaseGenerateOnlyDefault) {
  auto r = Parse(
      "module m;\n"
      "  case (MODE)\n"
      "    default: assign out = 0;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->gen_case_items.size(), 1u);
  EXPECT_TRUE(gen->gen_case_items[0].is_default);
}

TEST(GenerateInstantiationGrammar, CaseGenerateNested) {
  auto r = Parse(
      "module m;\n"
      "  case (A)\n"
      "    0: case (B)\n"
      "         0: assign out = 0;\n"
      "         default: assign out = 1;\n"
      "       endcase\n"
      "    default: assign out = 2;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateCase);
  ASSERT_GE(gen->gen_case_items.size(), 2u);
}

TEST(GenerateInstantiationGrammar, IfGenerateInsideCaseGenerate) {
  auto r = Parse(
      "module m;\n"
      "  case (MODE)\n"
      "    0: if (EN) assign out = in;\n"
      "    default: assign out = 0;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateCase);
  ASSERT_GE(gen->gen_case_items[0].body.size(), 1u);
  EXPECT_EQ(gen->gen_case_items[0].body[0]->kind, ModuleItemKind::kGenerateIf);
}

// generate_block ::= ... | [ generate_block_identifier : ] begin ...
// The label may precede `begin` (first optional position in the production),
// distinct from the post-`begin` `: label` form exercised elsewhere.
TEST(GenerateInstantiationGrammar, GenerateBlockLabelBeforeBegin) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) blk : begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  EXPECT_EQ(gen->name, "blk");
  ASSERT_EQ(gen->gen_body.size(), 1u);
}

TEST(GenerateInstantiationGrammar, IfGenerateBlockLabelBeforeBegin) {
  auto r = Parse(
      "module m;\n"
      "  if (EN) g : begin\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  EXPECT_EQ(gen->name, "g");
}

TEST(GenerateInstantiationGrammar, DeeplyNestedGenerateFor) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 2; i++) begin : l1\n"
      "    for (genvar j = 0; j < 2; j++) begin : l2\n"
      "      for (genvar k = 0; k < 2; k++) begin : l3\n"
      "        assign out[i][j][k] = in[i][j][k];\n"
      "      end\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* l1 = r.cu->modules[0]->items[0];
  EXPECT_EQ(l1->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(l1->gen_body.size(), 1u);
  auto* l2 = l1->gen_body[0];
  EXPECT_EQ(l2->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(l2->gen_body.size(), 1u);
  auto* l3 = l2->gen_body[0];
  EXPECT_EQ(l3->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(l3->gen_body.size(), 1u);
}

// --- error conditions ---

// case_generate_item ::= constant_expression { , constant_expression }
//   : generate_block | default [ : ] generate_block
// The colon is mandatory for the non-default form (only the `default` form may
// omit it), so a pattern item with no colon before its body is rejected.
TEST(GenerateInstantiationGrammar, CaseGenerateItemMissingColonRejected) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    8 assign out = in;\n"
      "  endcase\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// if_generate_construct ::= if ( constant_expression ) generate_block
//   [ else generate_block ]
// The parentheses around the condition are required by the production.
TEST(GenerateInstantiationGrammar, IfGenerateMissingParenRejected) {
  auto r = Parse(
      "module m;\n"
      "  if EN\n"
      "    assign out = in;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}
