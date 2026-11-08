#include <gtest/gtest.h>

#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_config_reports.h"
#include "helpers_reported_error.h"

namespace {

TEST(ConfigInstanceClause, InstancePathStartingOutsideDesignIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance other.a liblist work;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance path 'other.a' in config 'c' does not "
                            "start at a top-level cell",
                            4, "33.4.1.3"));
}

TEST(ConfigInstanceClause, InstancePathStartingAtDesignCellAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a liblist work;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigInstanceClause, BareTopLevelInstancePathAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top liblist work;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigInstanceClause, InstancePathPicksAmongMultipleDesignCells) {
  ElabFixture f;
  ElaborateSrc(
      "module top1; endmodule\n"
      "module top2; endmodule\n"
      "config c;\n"
      "  design top1 top2;\n"
      "  instance top2.x liblist work;\n"
      "endconfig\n",
      f, "top1");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigInstanceClause, DeepInstancePathRootedAtDesignCellAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a.b.c liblist work;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigInstanceClause, InstancePathRootMatchesLibraryQualifiedDesignCell) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design lib1.top;\n"
      "  instance top.a liblist work;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigInstanceClause, InstancePathRootedAtLibraryNameRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design lib1.top;\n"
      "  instance lib1.a liblist work;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance path 'lib1.a' in config 'c' does not "
                            "start at a top-level cell",
                            4, "33.4.1.3"));
}

std::string_view ModuleBoundInBlock(const ConfigElaboration& run,
                                    std::string_view block,
                                    std::string_view inst_name) {
  if (run.design == nullptr || run.design->top_modules.size() != 1) return {};
  for (const auto& child : run.design->top_modules[0]->children) {
    if (child.simple_inst_name != inst_name || child.resolved == nullptr ||
        child.gen_block_path.size() != 1 ||
        child.gen_block_path[0].name != block) {
      continue;
    }
    return child.resolved->name;
  }
  return {};
}

TEST(ConfigInstanceClause, InstancePathThroughAGenerateBlockIsApplied) {
  ConfigElaboration run;
  ElaborateUnderConfig(
      "module m; endmodule\n"
      "module m_gate; endmodule\n"
      "module top;\n"
      "  if (1) begin : g\n"
      "    m u();\n"
      "  end\n"
      "endmodule\n"
      "config cfg;\n"
      "  design work.top;\n"
      "  instance top.g.u use work.m_gate;\n"
      "endconfig\n",
      run);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(ModuleBoundInBlock(run, "g", "u"), "m_gate");
}

TEST(ConfigInstanceClause, FlattenedGenerateNameSelectsNothing) {
  ConfigElaboration run;
  ElaborateUnderConfig(
      "module m; endmodule\n"
      "module m_gate; endmodule\n"
      "module top;\n"
      "  if (1) begin : g\n"
      "    m u();\n"
      "  end\n"
      "endmodule\n"
      "config cfg;\n"
      "  design work.top;\n"
      "  instance top.g_u use work.m_gate;\n"
      "endconfig\n",
      run);
  EXPECT_EQ(ModuleBoundInBlock(run, "g", "u"), "m");
}

TEST(ConfigInstanceClause, LiblistThroughAGenerateBlockGovernsTheInstance) {
  auto diags = ConfigElaborationReports(
      "module m; endmodule\n"
      "module top;\n"
      "  if (1) begin : g\n"
      "    m u();\n"
      "  end\n"
      "endmodule\n"
      "config cfg;\n"
      "  design work.top;\n"
      "  instance top.g.u liblist gateLib;\n"
      "endconfig\n");
  EXPECT_TRUE(ReportedError(
      diags, "library list (gateLib) holds no cell 'm' for instance 'top.g.u'",
      4, "33.4.1.5"));
}

}  // namespace
