#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <utility>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/command_line_bind.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_config_reports.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/parser.h"

namespace {

struct BindAdderInputs {
  SourceManager& mgr;
  Arena& arena;
  DiagEngine& diag;
  const std::string& config_body;
  std::string_view la;
  std::string_view lb;
  std::string_view lt;
};

CompilationUnit* ParseAdderUnit(const BindAdderInputs& in) {
  std::string src;
  src += "module adder; endmodule\n";
  src += "module alt; endmodule\n";
  src += "module top; adder u(); endmodule\n";
  src += in.config_body;
  auto fid = in.mgr.AddFile("<test>", std::move(src));
  Lexer lex(in.mgr.FileContent(fid), fid, in.diag);
  Parser parser(lex, in.arena, in.diag);
  auto* cu = parser.Parse();
  cu->modules[0]->library = in.la;
  cu->modules[1]->library = in.lb;
  cu->modules[2]->library = in.lt;
  for (auto* cfg : cu->configs) cfg->library = in.lt;
  return cu;
}

RtlirModule* BindAdderChild(const BindAdderInputs& in) {
  auto* cu = ParseAdderUnit(in);
  Elaborator elab(in.arena, in.diag, cu);
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cell clause 'rtlLib.adder' uses a liblist "
                            "expansion",
                            4, "33.4.1.4"));
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

TEST(ConfigCellClause, LibQualifiedCellWithParameterResetAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  cell rtlLib.adder use #();\n"
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

TEST(ConfigCellClause, LibQualifiedCellClauseRebindsMatchingCell) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindAdderChild(
      {mgr, arena, diag,
       "config c; design top; cell rtlLib.adder use gateLib.alt; endconfig\n",
       "rtlLib", "gateLib", "rtlLib"});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "alt");
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigCellClause, UnqualifiedCellClauseAppliesToNamedCell) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindAdderChild(
      {mgr, arena, diag,
       "config c; design top; cell adder use gateLib.alt; endconfig\n",
       "rtlLib", "gateLib", "rtlLib"});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "alt");
  EXPECT_EQ(bound->library, "gateLib");
}

TEST(ConfigCellClause, CellClauseDoesNotApplyToUnnamedCell) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindAdderChild(
      {mgr, arena, diag,
       "config c; design top; cell alt use gateLib.alt; endconfig\n", "rtlLib",
       "gateLib", "rtlLib"});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "adder");
}

TEST(ConfigCellClause, LibQualifiedCellClauseDoesNotApplyToOtherLibraries) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindAdderChild(
      {mgr, arena, diag,
       "config c; design top; cell zzzLib.adder use gateLib.alt; endconfig\n",
       "rtlLib", "gateLib", "rtlLib"});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "adder");
}

constexpr std::string_view kCellClauseToAConfig =
    "module adder; endmodule\n"
    "module adder_gate; endmodule\n"
    "module top; adder a1(); adder a2(); endmodule\n"
    "config cfg;\n"
    "  design work.top;\n"
    "  cell adder use work.sub:config;\n"
    "endconfig\n"
    "config sub;\n"
    "  design work.adder_gate;\n"
    "endconfig\n";

TEST(ConfigCellClause, CellUseNamingAConfigBindsItsDesignCell) {
  ConfigElaboration run;
  ElaborateUnderConfig(kCellClauseToAConfig, run);
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_NE(run.design, nullptr);
  ASSERT_EQ(run.design->top_modules.size(), 1u);
  const auto& children = run.design->top_modules[0]->children;
  ASSERT_EQ(children.size(), 2u);
  for (const auto& child : children) {
    ASSERT_NE(child.resolved, nullptr) << child.inst_name;
    EXPECT_EQ(child.resolved->name, "adder_gate") << child.inst_name;
  }
}

TEST(ConfigCellClause, ConfigACellClauseNamesIsNotInForce) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", std::string(kCellClauseToAConfig));
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_NE(cu, nullptr);
  auto in_force = ConfigsInForce(*cu);
  ASSERT_EQ(in_force.size(), 1u);
  EXPECT_EQ(in_force[0]->name, "cfg");
}

std::string WidthsOfEachChild(const ConfigElaboration& run) {
  std::string out;
  if (run.design == nullptr || run.design->top_modules.size() != 1) return out;
  for (const auto& child : run.design->top_modules[0]->children) {
    if (child.resolved == nullptr) continue;
    for (const auto& p : child.resolved->params) {
      if (p.name != "W") continue;
      out += std::string(child.inst_name) + "=" +
             std::to_string(p.resolved_value) + " ";
    }
  }
  return out;
}

TEST(ConfigCellClause, ParameterOnlyUseOverridesEveryInstance) {
  ConfigElaboration run;
  ElaborateUnderConfig(
      "module adder #(parameter ID = 0, W = 8); endmodule\n"
      "module top; adder #(.ID(1)) x(); adder #(.ID(2)) y(); endmodule\n"
      "config cfg;\n"
      "  design work.top;\n"
      "  cell adder use #(.W(12));\n"
      "endconfig\n",
      run);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(WidthsOfEachChild(run), "x=12 y=12 ");
}

TEST(ConfigCellClause, CellAndParameterUseOverridesTheInstance) {
  ConfigElaboration run;
  ElaborateUnderConfig(
      "module adder #(parameter ID = 0, W = 8); endmodule\n"
      "module top; adder #(.ID(1)) x(); endmodule\n"
      "config cfg;\n"
      "  design work.top;\n"
      "  cell adder use work.adder #(.W(12));\n"
      "endconfig\n",
      run);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(WidthsOfEachChild(run), "x=12 ");
}

TEST(ConfigCellClause, InstanceOverrideBeatsTheCellOverride) {
  ConfigElaboration run;
  ElaborateUnderConfig(
      "module adder #(parameter W = 8); endmodule\n"
      "module top; adder x(); adder y(); endmodule\n"
      "config cfg;\n"
      "  design work.top;\n"
      "  cell adder use #(.W(12));\n"
      "  instance top.y use #(.W(20));\n"
      "endconfig\n",
      run);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(WidthsOfEachChild(run), "x=12 y=20 ");
}

TEST(ConfigCellClause, LibQualifiedCellSkipsAnInstanceBoundElsewhere) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  std::string src =
      "module adder; endmodule\n"
      "module adder; endmodule\n"
      "module alt; endmodule\n"
      "module top; adder u(); endmodule\n"
      "config c;\n"
      "  design rtlLib.top;\n"
      "  default liblist gateLib rtlLib;\n"
      "  cell aLib.adder use rtlLib.alt;\n"
      "endconfig\n";
  auto fid = mgr.AddFile("<test>", std::move(src));
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  cu->modules[0]->library = "gateLib";
  cu->modules[1]->library = "aLib";
  cu->modules[2]->library = "rtlLib";
  cu->modules[3]->library = "rtlLib";
  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_NE(design, nullptr);
  const RtlirModule* u = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->name, "adder");
  EXPECT_EQ(u->library, "gateLib");
}

}  // namespace
