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
  // The report stands at the line of the `config` keyword, not at the instance
  // clause: ValidateConfigInstanceClausesOne emits at `cfg->range.start`.
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

// Only the root segment of the hierarchical name is constrained to a design
// cell; the path below it may descend arbitrarily deep.
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

// When the design statement names the cell with a library qualifier, the root
// of an instance path matches the cell name rather than the library name.
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

// A library name is not a valid instance-path root; using it instead of the
// cell name is rejected.
TEST(ConfigInstanceClause, InstancePathRootedAtLibraryNameRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design lib1.top;\n"
      "  instance lib1.a liblist work;\n"
      "endconfig\n",
      f, "top");
  // The design statement contributes the cell name `top`, so the root `lib1`
  // matches no design cell. The report stands at the `config` keyword's line.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance path 'lib1.a' in config 'c' does not "
                            "start at a top-level cell",
                            4, "33.4.1.3"));
}

// The module bound to the instance named `inst_name` directly inside the
// generate block `block` of the design's one top, or empty where there is none.
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

// §33.4.1.3 (printed page 939): an instance clause names its instance by a
// SystemVerilog hierarchical name that begins at the config's top-level module,
// and §23.6 makes a generate block a level of such a name, so `top.g.u` names
// the instance u inside the block g and the clause rebinds it.
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

// The flattened name the instance is stored under, `g_u`, is not a
// hierarchical name of it, so a clause spelled that way selects nothing and
// the instance keeps the module it was written with.
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

// A library list a clause names for an instance inside a generate block is
// the list that instance is searched in (§33.4.1.5).
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
