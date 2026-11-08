#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

ParseResult ParseAndTagCells(const std::string& src) {
  ParseResult result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto preprocessed = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", preprocessed);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  MarkCellModules(result.cu, preproc.CellModuleNames());
  result.has_errors = diag.HasErrors();
  return result;
}

ModuleDecl* FindModule(const ParseResult& result, std::string_view name) {
  for (auto* mod : result.cu->modules) {
    if (mod->name == name) return mod;
  }
  return nullptr;
}

TEST(CelldefineParsing, ModuleInRegionIsTaggedAsCell) {
  auto result = ParseAndTagCells(
      "`celldefine\n"
      "module inv(output y, input a);\n"
      "  assign y = ~a;\n"
      "endmodule\n"
      "`endcelldefine\n");
  EXPECT_FALSE(result.has_errors);
  auto* inv = FindModule(result, "inv");
  ASSERT_NE(inv, nullptr);
  EXPECT_TRUE(inv->is_cell);
  EXPECT_EQ(inv->ports.size(), 2u);
}

TEST(CelldefineParsing, NonAnsiPortModuleIsTaggedAsCell) {
  auto result = ParseAndTagCells(
      "`celldefine\n"
      "module nonansi(a, y);\n"
      "  input a;\n"
      "  output y;\n"
      "  assign y = ~a;\n"
      "endmodule\n"
      "`endcelldefine\n");
  EXPECT_FALSE(result.has_errors);
  auto* nonansi = FindModule(result, "nonansi");
  ASSERT_NE(nonansi, nullptr);
  EXPECT_TRUE(nonansi->is_non_ansi_ports);
  EXPECT_TRUE(nonansi->is_cell);
}

TEST(CelldefineParsing, UnpairedCelldefineStillTagsModules) {
  auto result = ParseAndTagCells(
      "module leading_plain;\n"
      "endmodule\n"
      "`celldefine\n"
      "module first_cell;\n"
      "endmodule\n"
      "module last_cell;\n"
      "endmodule\n");
  EXPECT_FALSE(result.has_errors);
  ASSERT_NE(FindModule(result, "leading_plain"), nullptr);
  ASSERT_NE(FindModule(result, "first_cell"), nullptr);
  ASSERT_NE(FindModule(result, "last_cell"), nullptr);
  EXPECT_FALSE(FindModule(result, "leading_plain")->is_cell);
  EXPECT_TRUE(FindModule(result, "first_cell")->is_cell);
  EXPECT_TRUE(FindModule(result, "last_cell")->is_cell);
}

TEST(CelldefineParsing, MultiplePairsTagOnlyTheirOwnModules) {
  auto result = ParseAndTagCells(
      "`celldefine\n"
      "module cell_a;\n"
      "endmodule\n"
      "`endcelldefine\n"
      "module plain_b;\n"
      "endmodule\n"
      "`celldefine\n"
      "module cell_c(input logic clk);\n"
      "endmodule\n"
      "`endcelldefine\n");
  EXPECT_FALSE(result.has_errors);
  ASSERT_NE(FindModule(result, "cell_a"), nullptr);
  ASSERT_NE(FindModule(result, "plain_b"), nullptr);
  ASSERT_NE(FindModule(result, "cell_c"), nullptr);
  EXPECT_TRUE(FindModule(result, "cell_a")->is_cell);
  EXPECT_FALSE(FindModule(result, "plain_b")->is_cell);
  EXPECT_TRUE(FindModule(result, "cell_c")->is_cell);
}

TEST(CelldefineParsing, DirectiveInsideModuleBodyStillParses) {
  auto result = ParseAndTagCells(
      "`celldefine\n"
      "module t;\n"
      "  logic [3:0] q;\n"
      "`endcelldefine\n"
      "  initial q = 4'h5;\n"
      "endmodule\n"
      "module after_t;\n"
      "endmodule\n");
  EXPECT_FALSE(result.has_errors);
  auto* t = FindModule(result, "t");
  auto* after_t = FindModule(result, "after_t");
  ASSERT_NE(t, nullptr);
  ASSERT_NE(after_t, nullptr);
  EXPECT_TRUE(t->is_cell);
  EXPECT_FALSE(after_t->is_cell);
  EXPECT_FALSE(t->items.empty());
}

TEST(CelldefineParsing, ResetallClearsTheCellTag) {
  auto result = ParseAndTagCells(
      "`celldefine\n"
      "module before_reset;\n"
      "endmodule\n"
      "`resetall\n"
      "module after_reset;\n"
      "endmodule\n");
  EXPECT_FALSE(result.has_errors);
  ASSERT_NE(FindModule(result, "before_reset"), nullptr);
  ASSERT_NE(FindModule(result, "after_reset"), nullptr);
  EXPECT_TRUE(FindModule(result, "before_reset")->is_cell);
  EXPECT_FALSE(FindModule(result, "after_reset")->is_cell);
}

}  // namespace
