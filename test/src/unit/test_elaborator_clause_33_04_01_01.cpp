#include "fixture_elaborator.h"

namespace {

// §33.4.1.1 item 3: a config's design cell cannot itself name a
// configuration.
TEST(ConfigDesignStatement, DesignCellNamingConfigIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module dummy; endmodule\n"
      "config inner;\n"
      "  design dummy;\n"
      "endconfig\n"
      "config outer;\n"
      "  design inner;\n"
      "endconfig\n",
      f, "dummy");
  EXPECT_TRUE(f.has_errors);
}

// §33.4.1.1 item 6: when the library identifier is omitted on a design
// cell, the library that contains the config is used.  After
// elaboration the empty `lib` half of the design_cells entry should
// have been resolved to the config's own library.
TEST(ConfigDesignStatement, OmittedLibraryDefaultsToConfigLibrary) {
  delta::SourceManager mgr;
  delta::Arena arena;
  delta::DiagEngine diag(mgr);
  auto fid = mgr.AddFile(
      "<test>",
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "endconfig\n");
  delta::Lexer lexer(mgr.FileContent(fid), fid, diag);
  delta::Parser parser(lexer, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->configs.size(), 1u);

  // Stand in for the §33.3.3 library tag so the elaborator can resolve
  // the omitted library identifier without a real LibraryMap.
  cu->configs[0]->library = "myLib";

  delta::Elaborator elab(arena, diag, cu);
  elab.Elaborate("top");
  EXPECT_FALSE(diag.HasErrors());

  ASSERT_EQ(cu->configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(cu->configs[0]->design_cells[0].first, "myLib");
  EXPECT_EQ(cu->configs[0]->design_cells[0].second, "top");
}

}  // namespace
