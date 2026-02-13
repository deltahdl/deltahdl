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
  CompilationUnit* cu = nullptr;
};

static ParseResult Parse(const std::string& src) {
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

// --- Single-item generate-if without begin/end (§27.5) ---

TEST(ParserSection27, GenerateIfSingleItem) {
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
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kContAssign);
  EXPECT_EQ(gen->gen_else, nullptr);
}

TEST(ParserSection27, GenerateIfElseSingleItem) {
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
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kContAssign);
  ASSERT_NE(gen->gen_else, nullptr);
  ASSERT_EQ(gen->gen_else->gen_body.size(), 1);
  EXPECT_EQ(gen->gen_else->gen_body[0]->kind, ModuleItemKind::kContAssign);
}

// --- genvar declaration as module item (§27.4) ---

TEST(ParserSection27, GenvarDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  // genvar declaration should be consumed (stored as VarDecl or skipped).
  // The for loop should also parse.
  ASSERT_GE(mod->items.size(), 1);
  // The generate-for is present.
  bool found_gen_for = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) {
      found_gen_for = true;
    }
  }
  EXPECT_TRUE(found_gen_for);
}

// --- Inline genvar in generate-for init (§27.4) ---

TEST(ParserSection27, InlineGenvarInForInit) {
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
  ASSERT_EQ(gen->gen_body.size(), 1);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kContAssign);
}

// --- Generate-for with i++ step (§27.4) ---

TEST(ParserSection27, GenerateForPostIncrement) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen->gen_step, nullptr);
  ASSERT_EQ(gen->gen_body.size(), 1);
}

// --- Generate-case (§27.6) ---

TEST(ParserSection27, GenerateCase) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    1: assign out = in;\n"
      "    2: assign out = in2;\n"
      "    default: assign out = 0;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateCase);
  ASSERT_EQ(gen->gen_case_items.size(), 3u);
  EXPECT_FALSE(gen->gen_case_items[0].is_default);
  EXPECT_FALSE(gen->gen_case_items[1].is_default);
  EXPECT_TRUE(gen->gen_case_items[2].is_default);
}

// --- Generate-for with labeled begin/end (§27.4) ---

TEST(ParserSection27, GenerateForLabeled) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : gen_blk\n"
      "    assign out[i] = in[i];\n"
      "  end : gen_blk\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1u);
}

// --- Generate-if with begin/end blocks (§27.5) ---

TEST(ParserSection27, GenerateIfBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH > 1) begin\n"
      "    assign a = b;\n"
      "    assign c = d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_GE(gen->gen_body.size(), 2u);
}

// --- Generate-if/else-if chain (§27.5) ---

TEST(ParserSection27, GenerateIfElseIfChain) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH == 1)\n"
      "    assign out = a;\n"
      "  else if (WIDTH == 2)\n"
      "    assign out = b;\n"
      "  else\n"
      "    assign out = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_NE(gen->gen_else, nullptr);
  EXPECT_EQ(gen->gen_else->kind, ModuleItemKind::kGenerateIf);
  ASSERT_NE(gen->gen_else->gen_else, nullptr);
}

// --- generate...endgenerate wrapper (§27.3) ---

TEST(ParserSection27, GenerateRegion) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    for (genvar i = 0; i < 4; i++) begin\n"
      "      assign out[i] = in[i];\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  bool found_gen_for = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) found_gen_for = true;
  }
  EXPECT_TRUE(found_gen_for);
}

TEST(ParserSection27, GenerateForCompoundAssign) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i += 1) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen->gen_step, nullptr);
  ASSERT_EQ(gen->gen_body.size(), 1);
}
