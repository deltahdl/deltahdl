#include "fixture_parser.h"

using namespace delta;

// §22.10: `celldefine and `endcelldefine tag modules as cell modules. The
// preprocessor recognizes the directives and records which module headers fell
// inside an open region; the tag itself lands on the module declaration the
// parser built, as ModuleDecl::is_cell. That flag is the observable form of
// the tag, so the checks here drive real module source through preprocessing
// and parsing and read the flag off the resulting declarations.
//
// The directives carry no tokens of their own into the token stream, so the
// parser has no grammar rule for them; what it must show is that a tagged
// module is otherwise an ordinary module, and that an untagged one stays
// untagged.

namespace {

// Preprocesses and parses `src`, then hands the collected cell-module names to
// the production tagging routine. Going through delta::MarkCellModules rather
// than a copy of the match inside the test keeps what these checks observe on
// the production path.
ParseResult ParseAndTagCells(const std::string& src) {
  ParseResult result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto preprocessed = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", preprocessed);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
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

// C1: a module declared between the directives reaches the parser as a cell
// module, and it is still a fully formed module declaration -- the port count
// shows the directives contributed no tokens of their own to the stream.
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

// C1: a non-ANSI header takes a different path through the parser than the
// ANSI one above, and the tag has to land on the declaration either way.
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

// C2: the two directives are independent, so a `celldefine that is never
// closed still tags every module that follows it -- the tag does not depend on
// a matching `endcelldefine arriving later.
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

// C3/C4: more than one pair may appear, and the nearest preceding directive is
// what decides each module's tag.
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

// C5: the directives may sit inside a design element. Placing `endcelldefine
// in a module body is only discouraged, so the module parses normally, keeps
// its items, and is still the cell its opening `celldefine made it.
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

// C6: `resetall carries the `endcelldefine effect, so the module after it is
// not a cell while the one before it is.
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
