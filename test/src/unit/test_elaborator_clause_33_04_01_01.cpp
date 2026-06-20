#include "fixture_elaborator.h"

namespace {

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

TEST(ConfigDesignStatement, DesignCellSharingNameWithConfigIsAccepted) {
  // §33.4.1.1: a design cell may carry the same name as a config. Here a
  // module and a config both named 'shared' exist; the design statement names
  // 'shared', which denotes the module, not the config, and must be accepted.
  // The config is placed in a different library so it does not collide with
  // the module under the duplicate-definition check.
  delta::SourceManager mgr;
  delta::Arena arena;
  delta::DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>",
                         "module shared; endmodule\n"
                         "config shared;\n"
                         "  design shared;\n"
                         "endconfig\n");
  delta::Lexer lexer(mgr.FileContent(fid), fid, diag);
  delta::Parser parser(lexer, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->configs.size(), 1u);

  cu->configs[0]->library = "altLib";

  delta::Elaborator elab(arena, diag, cu);
  elab.Elaborate("shared");
  EXPECT_FALSE(diag.HasErrors());
}

TEST(ConfigDesignStatement, OmittedLibraryDefaultsToConfigLibrary) {
  delta::SourceManager mgr;
  delta::Arena arena;
  delta::DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>",
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

  cu->configs[0]->library = "myLib";

  delta::Elaborator elab(arena, diag, cu);
  elab.Elaborate("top");
  EXPECT_FALSE(diag.HasErrors());

  ASSERT_EQ(cu->configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(cu->configs[0]->design_cells[0].first, "myLib");
  EXPECT_EQ(cu->configs[0]->design_cells[0].second, "top");
}

TEST(ConfigDesignStatement, ExplicitLibraryIsNotOverridden) {
  // §33.4.1.1: the config's own library is substituted only when the design
  // cell omits its library qualifier. An explicit qualifier must survive
  // elaboration unchanged.
  delta::SourceManager mgr;
  delta::Arena arena;
  delta::DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>",
                         "module top; endmodule\n"
                         "config c;\n"
                         "  design work.top;\n"
                         "endconfig\n");
  delta::Lexer lexer(mgr.FileContent(fid), fid, diag);
  delta::Parser parser(lexer, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->configs.size(), 1u);

  cu->configs[0]->library = "otherLib";

  delta::Elaborator elab(arena, diag, cu);
  elab.Elaborate("top");
  EXPECT_FALSE(diag.HasErrors());

  ASSERT_EQ(cu->configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(cu->configs[0]->design_cells[0].first, "work");
  EXPECT_EQ(cu->configs[0]->design_cells[0].second, "top");
}

}  // namespace
