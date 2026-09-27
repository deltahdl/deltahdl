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

// Inputs for BindAdderChild, bundled to keep the helper parameter list small.
struct BindAdderInputs {
  SourceManager& mgr;
  Arena& arena;
  DiagEngine& diag;
  const std::string& config_body;
  std::string_view la;
  std::string_view lb;
  std::string_view lt;
};

// Parses `adder`, `alt`, and a `top` that instantiates `adder` under the
// supplied config body, then tags the three modules with libraries la/lb/lt.
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
  return cu;
}

// Config-elaborates the parsed unit and returns the cell bound to top.u, so a
// library-qualified cell clause can be observed through Elaborate(ConfigDecl).
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
  // The report stands at the line of the `config` keyword, not at the cell
  // clause: ValidateConfigCellClauses emits at `cfg->range.start`.
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
      {mgr, arena, diag,
       "config c; design top; cell rtlLib.adder use gateLib.alt; endconfig\n",
       "rtlLib", "gateLib", "rtlLib"});
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
      {mgr, arena, diag,
       "config c; design top; cell adder use gateLib.alt; endconfig\n",
       "rtlLib", "gateLib", "rtlLib"});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "alt");
  EXPECT_EQ(bound->library, "gateLib");
}

// §33.4.1.4: a cell clause applies only to the cell it names; an instance of a
// different cell is untouched even when the named cell exists. Here top.u is an
// adder, but the clause names 'alt', so the instance binds to adder unchanged.
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

// §33.4.1.4: the qualifying library scopes the clause; when that library does
// not define the named cell, the clause matches nothing and the cell binds
// normally.
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

// A cell clause handing every adder to a config whose design statement binds
// adder_gate, with the config written ahead of the one using it.
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

// §33.4.1.4 has a cell clause's expansion apply to every instance bound to the
// cell, and §33.4.2 has a use clause naming a config bind what that config's
// design statement names, so both adders become adder_gate.
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

// The config a cell clause hands its instances to is delegated to, like one an
// instance clause names, so it is not a second configuration in force.
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

// W as elaborated for each child of the design's one top, by instance name.
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

// §33.4.1.4 with Syntax 33-4's second use_clause form: a cell clause whose use
// expansion carries named parameter assignments alone keeps the cell and
// overrides the parameter on every instance of it.
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

// The third form names the cell as well as the assignments; the binding and
// the override both reach the instance.
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

// An instance clause is the more specific selection, so where it and a cell
// clause both set a parameter of one instance, the instance clause decides.
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

}  // namespace
