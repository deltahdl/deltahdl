#include <gtest/gtest.h>

#include <cstddef>
#include <initializer_list>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "helpers_config_reports.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct BindOnlyChildArgs {
  SourceManager& mgr;
  Arena& arena;
  DiagEngine& diag;
  const std::string& src;
  std::string_view lib0;
  std::string_view lib1;
  std::string_view lib2;
};

CompilationUnit* ParseWithLibraries(const BindOnlyChildArgs& args) {
  auto fid = args.mgr.AddFile("<test>", args.src);
  Lexer lex(args.mgr.FileContent(fid), fid, args.diag);
  Parser parser(lex, args.arena, args.diag);
  auto* cu = parser.Parse();
  cu->modules[0]->library = args.lib0;
  cu->modules[1]->library = args.lib1;
  cu->modules[2]->library = args.lib2;
  PlaceConfigsWithTheirTops(cu);
  return cu;
}

RtlirModule* BindOnlyChild(const BindOnlyChildArgs& args) {
  auto* cu = ParseWithLibraries(args);
  Elaborator elab(args.arena, args.diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  EXPECT_NE(design, nullptr);
  if (design == nullptr) return nullptr;
  EXPECT_EQ(design->top_modules.size(), 1u);
  if (design->top_modules.empty()) return nullptr;
  auto* top = design->top_modules[0];
  EXPECT_EQ(top->children.size(), 1u);
  if (top->children.empty()) return nullptr;
  return top->children[0].resolved;
}

constexpr const char* kSubUsesWidget =
    "module widget; endmodule\n"
    "module widget; endmodule\n"
    "module top; sub u(); endmodule\n"
    "config c; design top; cell sub use widget; endconfig\n";

TEST(ConfigUseClause, UseWithoutLibraryInheritsParentLibrary) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindOnlyChild(
      {mgr, arena, diag, kSubUsesWidget, "mainLib", "otherLib", "mainLib"});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "widget");
  EXPECT_EQ(bound->library, "mainLib");
}

TEST(ConfigUseClause, InheritedUseLibraryTracksParent) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindOnlyChild(
      {mgr, arena, diag, kSubUsesWidget, "mainLib", "otherLib", "otherLib"});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "widget");
  EXPECT_EQ(bound->library, "otherLib");
}

TEST(ConfigUseClause, UseDoesNotAlterLibraryList) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>",
                         "module w2; endmodule\n"
                         "module other; endmodule\n"
                         "module top; w x(); other o(); endmodule\n"
                         "config c; design top; default liblist libA;"
                         " cell w use libB.w2; endconfig\n");
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  cu->modules[0]->library = "libB";
  cu->modules[1]->library = "libB";
  cu->modules[2]->library = "libA";
  PlaceConfigsWithTheirTops(cu);

  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 2u);
  auto* w_bound = top->children[0].resolved;
  ASSERT_NE(w_bound, nullptr);
  EXPECT_EQ(w_bound->name, "w2");
  EXPECT_EQ(w_bound->library, "libB");
  EXPECT_EQ(top->children[1].resolved, nullptr);
}

TEST(ConfigUseClause, UseToMissingTargetLeavesInstanceUnbound) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>",
                         "module top; sub u(); endmodule\n"
                         "config c; design top;"
                         " cell sub use libB.absent; endconfig\n");
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  cu->modules[0]->library = "mainLib";
  PlaceConfigsWithTheirTops(cu);

  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
}

TEST(ConfigUseClause, ConfigSuffixSelectsConfigurationNotSameNamedModule) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>",
                         "module leaf; endmodule\n"
                         "module leaf; endmodule\n"
                         "module bot; leaf lf(); endmodule\n"
                         "module top; bot b(); endmodule\n"
                         "config c;\n"
                         "  design top;\n"
                         "  default liblist libA;\n"
                         "  instance top.b use lib1.bot:config;\n"
                         "endconfig\n"
                         "config bot;\n"
                         "  design lib1.bot;\n"
                         "  default liblist libB;\n"
                         "endconfig\n");
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 4u);
  cu->modules[0]->library = "libA";
  cu->modules[1]->library = "libB";
  cu->modules[2]->library = "lib1";
  cu->modules[3]->library = "libTop";
  PlaceConfigsWithTheirTops(cu);

  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);

  auto* bot = top->children[0].resolved;
  ASSERT_NE(bot, nullptr);
  EXPECT_EQ(bot->name, "bot");
  EXPECT_EQ(bot->library, "lib1");

  ASSERT_EQ(bot->children.size(), 1u);
  auto* leaf = bot->children[0].resolved;
  ASSERT_NE(leaf, nullptr);
  EXPECT_EQ(leaf->library, "libB");
}

TEST(ConfigUseClause, InstanceUseClauseBindsExactLibraryAndCell) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>",
                         "module widget; endmodule\n"
                         "module widget; endmodule\n"
                         "module top; widget u(); endmodule\n"
                         "config c; design top;"
                         " instance top.u use libB.widget; endconfig\n");
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_FALSE(diag.HasErrors());
  cu->modules[0]->library = "libA";
  cu->modules[1]->library = "libB";
  cu->modules[2]->library = "libTop";
  PlaceConfigsWithTheirTops(cu);

  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "widget");
  EXPECT_EQ(bound->library, "libB");
}

TEST(ConfigUseClause, InstanceUseWithoutLibraryInheritsParentLibrary) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>",
                         "module bar; endmodule\n"
                         "module foo; endmodule\n"
                         "module top; foo u(); endmodule\n"
                         "config c; design top;"
                         " instance top.u use bar; endconfig\n");
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_FALSE(diag.HasErrors());
  cu->modules[0]->library = "libP";
  cu->modules[1]->library = "libP";
  cu->modules[2]->library = "libP";
  PlaceConfigsWithTheirTops(cu);

  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "bar");
  EXPECT_EQ(bound->library, "libP");
}

TEST(ConfigUseClause, UseNamingNoCellReportsTheClausesTarget) {
  auto diags = ConfigElaborationReports(
      "module adder; endmodule\n"
      "module top; adder a1(); endmodule\n"
      "config cfg; design work.top; instance top.a1 use work.nosuch; "
      "endconfig\n");
  EXPECT_TRUE(ReportedError(diags, "library 'work' holds no cell 'nosuch'", 2,
                            "33.4.1.6"));
}

TEST(ConfigUseClause, UseNamingAnAbsentLibraryReportsThatLibrary) {
  auto diags = ConfigElaborationReports(
      "module adder; endmodule\n"
      "module top; adder a1(); endmodule\n"
      "config cfg; design work.top; instance top.a1 use gateLib.adder; "
      "endconfig\n");
  EXPECT_TRUE(ReportedError(diags, "library 'gateLib' holds no cell 'adder'", 2,
                            "33.4.1.6"));
}

RtlirDesign* ElaborateWithPrimitives(
    ConfigElaboration& run, const std::string& src,
    std::initializer_list<std::string_view> udp_libs, std::string_view lib) {
  auto fid = run.mgr.AddFile("<test>", src);
  Lexer lex(run.mgr.FileContent(fid), fid, run.diag);
  Parser parser(lex, run.arena, run.diag);
  auto* cu = parser.Parse();
  size_t i = 0;
  for (std::string_view udp_lib : udp_libs) cu->udps[i++]->library = udp_lib;
  for (auto* mod : cu->modules) mod->library = lib;
  for (auto* cfg : cu->configs) cfg->library = lib;
  Elaborator elab(run.arena, run.diag, cu);
  return elab.Elaborate(cu->configs[0]);
}

TEST(ConfigUseClause, InstanceClauseBindsAnInstanceToAPrimitive) {
  ConfigElaboration run;
  auto* design = ElaborateWithPrimitives(
      run,
      "primitive prim(output o, input i); table 0:0; 1:1; endtable "
      "endprimitive\n"
      "module foo(output o, input i); assign o = i; endmodule\n"
      "module top; wire o, i; foo a(o, i); endmodule\n"
      "config c; design work.top; instance top.a use prim; endconfig\n",
      {"work"}, "work");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(run.diag.HasErrors());
  const RtlirModule* top = design->top_modules[0];
  ASSERT_EQ(top->udp_insts.size(), 1u);
  EXPECT_EQ(top->udp_insts[0].decl->name, "prim");
}

TEST(ConfigUseClause, InstanceClauseReachesAnEarlierDeclaredPrimitive) {
  ConfigElaboration run;
  auto* design = ElaborateWithPrimitives(
      run,
      "primitive u_and(output o, input a); table 0:0; 1:1; endtable "
      "endprimitive\n"
      "primitive u_and(output o, input a); table 0:1; 1:0; endtable "
      "endprimitive\n"
      "module top; wire o, a; u_and u(o, a); endmodule\n"
      "config c; design rtlLib.top; default liblist rtlLib;\n"
      "  instance top.u liblist gateLib; endconfig\n",
      {"rtlLib", "gateLib"}, "rtlLib");
  ASSERT_NE(design, nullptr);
  const RtlirModule* top = design->top_modules[0];
  ASSERT_EQ(top->udp_insts.size(), 1u);
  EXPECT_EQ(top->udp_insts[0].decl->library, "gateLib");
}

}  // namespace
