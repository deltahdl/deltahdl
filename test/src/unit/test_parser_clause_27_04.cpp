// §27.4: Loop generate constructs

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A4GenerateForBlock) {
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

// --- loop_generate_construct: basic for loop ---
TEST(ParserAnnexA042, LoopGenerateBasic) {
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

// --- genvar_initialization: without genvar keyword (pre-declared) ---
TEST(ParserAnnexA042, GenvarInitWithoutGenvarKeyword) {
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

// --- genvar_iteration: assignment_operator (i = i + 1) ---
TEST(ParserAnnexA042, GenvarIterationAssignment) {
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

// --- genvar_iteration: genvar_identifier inc_or_dec_operator (i++) ---
TEST(ParserAnnexA042, GenvarIterationPostIncrement) {
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

// --- genvar_iteration: genvar_identifier dec_operator (i--) ---
TEST(ParserAnnexA042, GenvarIterationPostDecrement) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 3; i >= 0; i--) begin\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_NE(gen->gen_step, nullptr);
}

// --- generate_block: single generate_item (no begin/end) ---
TEST(ParserAnnexA042, GenerateBlockSingleItem) {
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

// --- generate_item: module_or_generate_item (module instantiation) ---
TEST(ParserAnnexA042, GenerateItemModuleInst) {
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

// --- nested generate constructs: for inside for ---
TEST(ParserAnnexA042, NestedForInsideFor) {
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

// =============================================================================
// LRM section 27.1 -- General (generate constructs overview)
// =============================================================================
// §27.1: Generate-for with module instantiation (structural repetition).
TEST(ParserSection27, GenerateForWithModuleInst2) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : gen_inst\n"
      "    sub u(.a(w[i]));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kModuleInst);
}

using ProgramParseTest = ProgramTestParse;

// =========================================================================
// LRM section 27.3: Generate construct syntax / generate regions
// =========================================================================
TEST(ParserSection23, GenerateRegionWithFor) {
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

// §27.1: Generate-for with always block body.
TEST(ParserSection27, GenerateForWithAlwaysBlock) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : gen_alw\n"
      "    always @(posedge clk)\n"
      "      q[i] <= d[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kAlwaysBlock);
}

// =========================================================================
// LRM section 27.3: Generate block syntax (begin/end with labels)
// =========================================================================
TEST(ParserSection23, GenerateBlockNamedBeginEnd) {
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

TEST(Parser, GenerateFor) {
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

// §3.3 Generate blocks
TEST(ParserClause03, Cl3_3_GenerateBlocks) {
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

// 14. Generate block scope (for-generate)
TEST(ParserClause03, Cl3_13_GenerateForBlockScope) {
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

// =========================================================================
// LRM section 27.4: Loop generates
// =========================================================================
TEST(ParserSection23, LoopGenerateForStructure) {
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

TEST(ParserSection23, LoopGenerateInlineGenvar) {
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

TEST(ParserSection23, LoopGenerateWithModuleInst) {
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

// =========================================================================
// LRM section 27.4: Genvar declarations
// =========================================================================
TEST(ParserSection23, GenvarDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(mod->items[0]->name, "i");
}

TEST(ParserA213, GenvarDeclMultiple) {
  auto r = Parse("module m; genvar i, j, k; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
}

// --- list_of_genvar_identifiers ---
// genvar_identifier { , genvar_identifier }
TEST(ParserA23, ListOfGenvarIdentifiersSingle) {
  auto r = Parse("module m; genvar i; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "i");
}

TEST(ParserSection23, GenvarMultipleDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  genvar i, j, k;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 3);
  EXPECT_EQ(mod->items[0]->name, "i");
  EXPECT_EQ(mod->items[1]->name, "j");
  EXPECT_EQ(mod->items[2]->name, "k");
}

// =========================================================================
// LRM section 27.4: Genvar expressions in loop generate
// =========================================================================
TEST(ParserSection23, GenvarExprInLoopBound) {
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

TEST(ParserSection23, GenvarPostIncrementStep) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  for (genvar i = 0; i < 4; i++) begin : blk\n"
              "    assign a[i] = b[i];\n"
              "  end\n"
              "endmodule\n"));
}

// =========================================================================
// LRM section 27.4: Indexed generate block names
// =========================================================================
TEST(ParserSection23, IndexedGenerateBlockName) {
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

TEST(ParserSection23, EndLabelOnGenerateBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  genvar i;\n"
              "  for (i = 0; i < 4; i = i + 1) begin : blk\n"
              "    assign a[i] = b[i];\n"
              "  end : blk\n"
              "endmodule\n"));
}

// =========================================================================
// Combined / integration tests
// =========================================================================
TEST(ParserSection23, ParameterizedModuleWithGenerate) {
  auto r = Parse(
      "module gray2bin #(parameter SIZE = 8) (\n"
      "  output [SIZE-1:0] bin,\n"
      "  input [SIZE-1:0] gray);\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < SIZE; i = i + 1) begin : bitnum\n"
      "      assign bin[i] = ^gray[SIZE-1:i];\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "gray2bin");
  ASSERT_EQ(mod->params.size(), 1);
  EXPECT_EQ(mod->params[0].first, "SIZE");
  ASSERT_EQ(mod->ports.size(), 2);
}

TEST(ParserSection23, GenerateNestedLoops) {
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

TEST(ParserSection23, GenerateIfInsideForLoop) {
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

// =============================================================================
// A.8.3 Expressions — genvar_expression
// =============================================================================
// § genvar_expression ::= constant_expression (used in generate for)
TEST(ParserA83, GenvarExprInGenerateFor) {
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

// --- Single-item generate-for without begin/end (§27.4) ---
TEST(ParserSection27, GenerateForSingleItem) {
  auto r = Parse(
      "module m;\n"
      "  for (i = 0; i < 4; i = i + 1)\n"
      "    assign out[i] = in[i];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kContAssign);
}

// --- Inline genvar in generate-for init (§27.4) ---
TEST(ParserSection27, InlineGenvarInForInitParse) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i = i + 1) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen->gen_init, nullptr);
}

}  // namespace
