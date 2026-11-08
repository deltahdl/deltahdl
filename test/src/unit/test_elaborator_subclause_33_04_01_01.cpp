#include <gtest/gtest.h>

#include <filesystem>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/separate_compilation_bind.h"
#include "fixture_config_unit.h"
#include "fixture_elaborator.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"
#include "parser/library_map.h"
#include "parser/precompiled_library.h"

using namespace delta;
namespace fs = std::filesystem;

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'outer' design statement names "
                            "configuration 'inner'; design cells must not be "
                            "configs",
                            6, "33.4.1.1"));
}

TEST(ConfigDesignStatement,
     DesignCellNamingConfigAmongMultipleCellsIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m; endmodule\n"
      "config sub;\n"
      "  design m;\n"
      "endconfig\n"
      "config outer;\n"
      "  design m sub;\n"
      "endconfig\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'outer' design statement names "
                            "configuration 'sub'; design cells must not be "
                            "configs",
                            6, "33.4.1.1"));
}

TEST(ConfigDesignStatement, ReportStandsAtTheOffendingDesignCell) {
  ElabFixture f;
  ElaborateSrc(
      "module first; endmodule\n"
      "module second; endmodule\n"
      "config sub;\n"
      "  design first;\n"
      "endconfig\n"
      "config outer;\n"
      "  design first\n"
      "         second\n"
      "         sub;\n"
      "endconfig\n",
      f, "first");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'outer' design statement names "
                            "configuration 'sub'; design cells must not be "
                            "configs",
                            9, "33.4.1.1"));
}

TEST(ConfigDesignStatement, ProgramSharingNameWithConfigIsAccepted) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module top; endmodule\n"
              "program shared; endprogram\n"
              "config shared;\n"
              "  design shared;\n"
              "endconfig\n"));
  u.PlaceConfigInLibrary("altLib");
  u.ElaborateTop("top");
  EXPECT_FALSE(u.diag.HasErrors());
}

TEST(ConfigDesignStatement, DesignCellSharingNameWithConfigIsAccepted) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module shared; endmodule\n"
              "config shared;\n"
              "  design shared;\n"
              "endconfig\n"));
  u.PlaceConfigInLibrary("altLib");
  u.ElaborateTop("shared");
  EXPECT_FALSE(u.diag.HasErrors());
}

TEST(ConfigDesignStatement, OmittedLibraryDefaultsToConfigLibrary) {
  ScratchDir tmp;
  MappedConfigUnit u;
  ASSERT_TRUE(u.ParseUnderMap(tmp, "library myLib *.v;\n",
                              "module top; endmodule\n"
                              "config c;\n"
                              "  design top;\n"
                              "endconfig\n"));
  ASSERT_EQ(u.ConfigLibrary(), "myLib");
  u.ElaborateTop("top");
  EXPECT_FALSE(u.diag.HasErrors());

  ASSERT_EQ(u.cu->configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(u.cu->configs[0]->design_cells[0].library, "myLib");
  EXPECT_EQ(u.cu->configs[0]->design_cells[0].cell, "top");
}

TEST(ConfigDesignStatement, ExplicitLibraryIsNotOverridden) {
  ScratchDir tmp;
  MappedConfigUnit u;
  ASSERT_TRUE(u.ParseUnderMap(tmp, "library otherLib *.v;\n",
                              "module top; endmodule\n"
                              "config c;\n"
                              "  design work.top;\n"
                              "endconfig\n"));
  ASSERT_EQ(u.ConfigLibrary(), "otherLib");
  u.ElaborateTop("top");
  EXPECT_FALSE(u.diag.HasErrors());

  ASSERT_EQ(u.cu->configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(u.cu->configs[0]->design_cells[0].library, "work");
  EXPECT_EQ(u.cu->configs[0]->design_cells[0].cell, "top");
}

TEST(ConfigDesignStatement, MixedOmittedAndExplicitLibrariesResolvedPerCell) {
  ScratchDir tmp;
  MappedConfigUnit u;
  ASSERT_TRUE(u.ParseUnderMap(tmp, "library myLib *.v;\n",
                              "module c; endmodule\n"
                              "module d; endmodule\n"
                              "config cfg;\n"
                              "  design c work.d;\n"
                              "endconfig\n"));
  ASSERT_EQ(u.ConfigLibrary(), "myLib");
  u.ElaborateTop("c");
  EXPECT_FALSE(u.diag.HasErrors());

  ASSERT_EQ(u.cu->configs[0]->design_cells.size(), 2u);
  EXPECT_EQ(u.cu->configs[0]->design_cells[0].library, "myLib");
  EXPECT_EQ(u.cu->configs[0]->design_cells[0].cell, "c");
  EXPECT_EQ(u.cu->configs[0]->design_cells[1].library, "work");
  EXPECT_EQ(u.cu->configs[0]->design_cells[1].cell, "d");
}

TEST(ConfigDesignStatement, DesignCellNoLibraryHoldsIsReportedAtThatCell) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module m; endmodule\n"
              "config cfg;\n"
              "  design m\n"
              "         missing;\n"
              "endconfig\n"));
  EXPECT_EQ(u.ElaborateConfig(0), nullptr);
  EXPECT_TRUE(ReportedError(u.diag.Diagnostics(),
                            "config 'cfg' design cell 'missing' not found", 4,
                            "33.4.1.1"));
}

TEST(ConfigDesignStatement, OmittedLibrarySearchesOnlyTheConfigsLibrary) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module top; endmodule\n"
              "config c;\n"
              "  design top;\n"
              "endconfig\n"));
  u.cu->modules[0]->library = "libT";
  u.cu->configs[0]->library = "libC";
  EXPECT_EQ(u.ElaborateConfig(0), nullptr);
  EXPECT_TRUE(ReportedError(u.diag.Diagnostics(),
                            "config 'c' design cell 'top' not found in "
                            "library 'libC'",
                            3, "33.4.1.1"));
}

struct ConfigBindHarness {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  SeparateCompilationBinder binder{mgr, arena, diag};
};

TEST(ConfigDesignStatement, ConfigNamingNoDesignIsReportedAtItsDeclaration) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtl.dpl";
  ASSERT_TRUE(
      PrecompiledLibrary::Save("module top;\n"
                               "endmodule\n"
                               "config cfg_empty;\n"
                               "  design;\n"
                               "endconfig\n",
                               "rtlLib", path));

  ConfigBindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  EXPECT_EQ(h.binder.BindConfig("cfg_empty"), nullptr);
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "config 'cfg_empty' names no design", 3,
                            "33.4.1.1"));
}

}  // namespace
