#include "fixture_elaborator.h"

namespace {

// Config-elaborates `adder`, `alt`, and a `top` that instantiates `adder`
// (libraries set to la/lb/lt) under the supplied config body, and returns the
// cell bound to top.u, so a library-qualified cell clause can be observed
// through Elaborate(ConfigDecl).
RtlirModule* BindAdderChild(SourceManager& mgr, Arena& arena, DiagEngine& diag,
                            const std::string& config_body, std::string_view la,
                            std::string_view lb, std::string_view lt) {
  std::string src;
  src += "module adder; endmodule\n";
  src += "module alt; endmodule\n";
  src += "module top; adder u(); endmodule\n";
  src += config_body;
  auto fid = mgr.AddFile("<test>", std::move(src));
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  cu->modules[0]->library = la;
  cu->modules[1]->library = lb;
  cu->modules[2]->library = lt;
  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  EXPECT_NE(design, nullptr);
  return design->top_modules[0]->children[0].resolved;
}

TEST(ConfigCellClause, LibQualifiedCellWithLiblistRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  cell rtlLib.adder liblist gateLib;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(ConfigCellClause, UnqualifiedCellWithLiblistAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  cell adder liblist gateLib;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigCellClause, LibQualifiedCellWithUseClauseAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  cell rtlLib.adder use gateLib.alt;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// §33.4.1.4: a library-qualified cell clause applies to instances bound to the
// selected library and cell, so its use expansion rebinds the matching cell.
TEST(ConfigCellClause, LibQualifiedCellClauseRebindsMatchingCell) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindAdderChild(
      mgr, arena, diag,
      "config c; design top; cell rtlLib.adder use gateLib.alt; endconfig\n",
      "rtlLib", "gateLib", "rtlLib");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "alt");
  EXPECT_EQ(bound->library, "gateLib");
}

// §33.4.1.4: a cell selection clause names the cell it applies to; an
// unqualified clause applies to that cell whatever library holds it, so its
// use expansion rebinds the named cell.
TEST(ConfigCellClause, UnqualifiedCellClauseAppliesToNamedCell) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindAdderChild(
      mgr, arena, diag,
      "config c; design top; cell adder use gateLib.alt; endconfig\n", "rtlLib",
      "gateLib", "rtlLib");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "alt");
  EXPECT_EQ(bound->library, "gateLib");
}

// §33.4.1.4: the qualifying library scopes the clause; when that library does
// not define the named cell, the clause matches nothing and the cell binds
// normally.
TEST(ConfigCellClause, LibQualifiedCellClauseDoesNotApplyToOtherLibraries) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindAdderChild(
      mgr, arena, diag,
      "config c; design top; cell zzzLib.adder use gateLib.alt; endconfig\n",
      "rtlLib", "gateLib", "rtlLib");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "adder");
}

}  // namespace
