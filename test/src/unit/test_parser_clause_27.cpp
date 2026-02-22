#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// --- Single-item generate-for without begin/end (§27.4) ---

TEST(ParserSection27, GenerateForSingleItem) {
  auto r = Parse("module m;\n"
                 "  for (i = 0; i < 4; i = i + 1)\n"
                 "    assign out[i] = in[i];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto *gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kContAssign);
}

// --- Single-item generate-if without begin/end (§27.5) ---

TEST(ParserSection27, GenerateIfSingleItemParse) {
  auto r = Parse("module m;\n"
                 "  if (WIDTH > 1)\n"
                 "    assign out = in;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto *gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_EQ(gen->gen_body.size(), 1);
}

TEST(ParserSection27, GenerateIfSingleItemBody) {
  auto r = Parse("module m;\n"
                 "  if (WIDTH > 1)\n"
                 "    assign out = in;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kContAssign);
  EXPECT_EQ(gen->gen_else, nullptr);
}

TEST(ParserSection27, GenerateIfElseSingleItemParse) {
  auto r = Parse("module m;\n"
                 "  if (WIDTH > 1)\n"
                 "    assign out = a;\n"
                 "  else\n"
                 "    assign out = b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto *gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_EQ(gen->gen_body.size(), 1);
}

TEST(ParserSection27, GenerateIfElseSingleItemBranches) {
  auto r = Parse("module m;\n"
                 "  if (WIDTH > 1)\n"
                 "    assign out = a;\n"
                 "  else\n"
                 "    assign out = b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kContAssign);
  ASSERT_NE(gen->gen_else, nullptr);
  ASSERT_EQ(gen->gen_else->gen_body.size(), 1);
  EXPECT_EQ(gen->gen_else->gen_body[0]->kind, ModuleItemKind::kContAssign);
}

// --- genvar declaration as module item (§27.4) ---

TEST(ParserSection27, GenvarDeclaration) {
  auto r = Parse("module m;\n"
                 "  genvar i;\n"
                 "  for (i = 0; i < 4; i = i + 1) begin\n"
                 "    assign out[i] = in[i];\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  // genvar declaration should be consumed (stored as VarDecl or skipped).
  // The for loop should also parse.
  ASSERT_GE(mod->items.size(), 1);
  // The generate-for is present.
  bool found_gen_for = false;
  for (auto *item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) {
      found_gen_for = true;
    }
  }
  EXPECT_TRUE(found_gen_for);
}

// --- Inline genvar in generate-for init (§27.4) ---

TEST(ParserSection27, InlineGenvarInForInitParse) {
  auto r = Parse("module m;\n"
                 "  for (genvar i = 0; i < 4; i = i + 1) begin\n"
                 "    assign out[i] = in[i];\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto *gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen->gen_init, nullptr);
}

TEST(ParserSection27, InlineGenvarInForInitBody) {
  auto r = Parse("module m;\n"
                 "  for (genvar i = 0; i < 4; i = i + 1) begin\n"
                 "    assign out[i] = in[i];\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->gen_body.size(), 1);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kContAssign);
}

// --- Generate-for with i++ step (§27.4) ---

TEST(ParserSection27, GenerateForPostIncrement) {
  auto r = Parse("module m;\n"
                 "  for (genvar i = 0; i < 4; i++) begin\n"
                 "    assign out[i] = in[i];\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto *gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen->gen_step, nullptr);
  ASSERT_EQ(gen->gen_body.size(), 1);
}

// --- Generate-case (§27.6) ---

TEST(ParserSection27, GenerateCaseParse) {
  auto r = Parse("module m;\n"
                 "  case (WIDTH)\n"
                 "    1: assign out = in;\n"
                 "    2: assign out = in2;\n"
                 "    default: assign out = 0;\n"
                 "  endcase\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto *gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateCase);
  ASSERT_EQ(gen->gen_case_items.size(), 3u);
}

TEST(ParserSection27, GenerateCaseItemDefaults) {
  auto r = Parse("module m;\n"
                 "  case (WIDTH)\n"
                 "    1: assign out = in;\n"
                 "    2: assign out = in2;\n"
                 "    default: assign out = 0;\n"
                 "  endcase\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *gen = r.cu->modules[0]->items[0];
  const bool kExpectedDefaults[] = {false, false, true};
  for (size_t i = 0; i < 3; i++) {
    EXPECT_EQ(gen->gen_case_items[i].is_default, kExpectedDefaults[i]);
  }
}

// --- Generate-for with labeled begin/end (§27.4) ---

TEST(ParserSection27, GenerateForLabeled) {
  auto r = Parse("module m;\n"
                 "  for (genvar i = 0; i < 4; i++) begin : gen_blk\n"
                 "    assign out[i] = in[i];\n"
                 "  end : gen_blk\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto *gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1u);
}

// --- Generate-if with begin/end blocks (§27.5) ---

TEST(ParserSection27, GenerateIfBeginEnd) {
  auto r = Parse("module m;\n"
                 "  if (WIDTH > 1) begin\n"
                 "    assign a = b;\n"
                 "    assign c = d;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto *gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_GE(gen->gen_body.size(), 2u);
}

// --- Generate-if/else-if chain (§27.5) ---

TEST(ParserSection27, GenerateIfElseIfChainParse) {
  auto r = Parse("module m;\n"
                 "  if (WIDTH == 1)\n"
                 "    assign out = a;\n"
                 "  else if (WIDTH == 2)\n"
                 "    assign out = b;\n"
                 "  else\n"
                 "    assign out = c;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto *gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_NE(gen->gen_else, nullptr);
}

TEST(ParserSection27, GenerateIfElseIfChainNesting) {
  auto r = Parse("module m;\n"
                 "  if (WIDTH == 1)\n"
                 "    assign out = a;\n"
                 "  else if (WIDTH == 2)\n"
                 "    assign out = b;\n"
                 "  else\n"
                 "    assign out = c;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->gen_else->kind, ModuleItemKind::kGenerateIf);
  ASSERT_NE(gen->gen_else->gen_else, nullptr);
}

// --- generate...endgenerate wrapper (§27.3) ---

TEST(ParserSection27, GenerateRegion) {
  auto r = Parse("module m;\n"
                 "  generate\n"
                 "    for (genvar i = 0; i < 4; i++) begin\n"
                 "      assign out[i] = in[i];\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  bool found_gen_for = false;
  for (auto *item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateFor)
      found_gen_for = true;
  }
  EXPECT_TRUE(found_gen_for);
}

TEST(ParserSection27, GenerateForCompoundAssign) {
  auto r = Parse("module m;\n"
                 "  for (genvar i = 0; i < 4; i += 1) begin\n"
                 "    assign out[i] = in[i];\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto *gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen->gen_step, nullptr);
  ASSERT_EQ(gen->gen_body.size(), 1);
}

// --- generate...endgenerate with multiple constructs (§27.1/§27.3) ---

TEST(ParserSection27, GenerateOverview) {
  auto r = Parse("module m;\n"
                 "  generate\n"
                 "    if (A) assign x = 1;\n"
                 "    if (B) assign y = 2;\n"
                 "  endgenerate\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  size_t gen_if_count = 0;
  for (auto *item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateIf)
      ++gen_if_count;
  }
  EXPECT_EQ(gen_if_count, 2u);
}

TEST(ParserSection27, GenerateRegionWithMultipleKinds) {
  auto r = Parse("module m;\n"
                 "  generate\n"
                 "    for (genvar i = 0; i < 2; i++) begin\n"
                 "      assign a[i] = b[i];\n"
                 "    end\n"
                 "    if (WIDTH > 0)\n"
                 "      assign c = d;\n"
                 "  endgenerate\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  bool found_for = false;
  bool found_if = false;
  for (auto *item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateFor)
      found_for = true;
    if (item->kind == ModuleItemKind::kGenerateIf)
      found_if = true;
  }
  EXPECT_TRUE(found_for);
  EXPECT_TRUE(found_if);
}

// --- generate region empty (§27.3) ---

TEST(ParserSection27, GenerateRegionEmpty) {
  auto r = Parse("module m;\n"
                 "  generate\n"
                 "  endgenerate\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  EXPECT_TRUE(mod->items.empty());
}

// --- Loop generate with module instantiation (§27.4) ---

TEST(ParserSection27, GenerateForWithModuleInst) {
  auto r = Parse("module m;\n"
                 "  for (genvar i = 0; i < 4; i++) begin : blk\n"
                 "    sub u(.a(in[i]), .b(out[i]));\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kModuleInst);
}

TEST(ParserSection27, GenerateForNestedBeginEnd) {
  auto r = Parse("module m;\n"
                 "  for (genvar i = 0; i < 2; i++) begin : outer\n"
                 "    for (genvar j = 0; j < 2; j++) begin : inner\n"
                 "      assign out[i][j] = in[i][j];\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *outer = r.cu->modules[0]->items[0];
  EXPECT_EQ(outer->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(outer->gen_body.size(), 1u);
  EXPECT_EQ(outer->gen_body[0]->kind, ModuleItemKind::kGenerateFor);
}

TEST(ParserSection27, GenerateForPreDecrement) {
  auto r = Parse("module m;\n"
                 "  for (genvar i = 3; i >= 0; i--) begin\n"
                 "    assign out[i] = in[i];\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen->gen_step, nullptr);
}

// =============================================================================
// LRM section 27.1 -- General (generate constructs overview)
// =============================================================================

// §27.1: Generate-for with module instantiation (structural repetition).
TEST(ParserSection27, GenerateForWithModuleInst2) {
  auto r = Parse("module m;\n"
                 "  for (genvar i = 0; i < 4; i++) begin : gen_inst\n"
                 "    sub u(.a(w[i]));\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto *gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kModuleInst);
}

// §27.1: Generate-if with nested generate-for (hierarchical conditional).
TEST(ParserSection27, GenerateIfWithNestedFor) {
  auto r = Parse("module m;\n"
                 "  if (USE_PIPELINE) begin\n"
                 "    for (genvar i = 0; i < STAGES; i++) begin : stage\n"
                 "      assign pipe[i] = data[i];\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateIf);
  ASSERT_GE(mod->items[0]->gen_body.size(), 1u);
  EXPECT_EQ(mod->items[0]->gen_body[0]->kind, ModuleItemKind::kGenerateFor);
}

// §27.1: Multiple generate constructs in sequence.
TEST(ParserSection27, MultipleGenerateConstructs) {
  auto r = Parse("module m;\n"
                 "  for (genvar i = 0; i < 4; i++) begin : g1\n"
                 "    assign a[i] = b[i];\n"
                 "  end\n"
                 "  if (MODE) begin\n"
                 "    assign x = y;\n"
                 "  end\n"
                 "  case (SEL)\n"
                 "    0: assign out = a;\n"
                 "    default: assign out = b;\n"
                 "  endcase\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 3u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateFor);
  EXPECT_EQ(mod->items[1]->kind, ModuleItemKind::kGenerateIf);
  EXPECT_EQ(mod->items[2]->kind, ModuleItemKind::kGenerateCase);
}

// §27.1: Generate-for with always block body.
TEST(ParserSection27, GenerateForWithAlwaysBlock) {
  auto r = Parse("module m;\n"
                 "  for (genvar i = 0; i < 4; i++) begin : gen_alw\n"
                 "    always @(posedge clk)\n"
                 "      q[i] <= d[i];\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kAlwaysBlock);
}
