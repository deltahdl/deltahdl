#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <initializer_list>
#include <string>
#include <string_view>
#include <utility>

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

struct BindLeafParams {
  const std::string& config_body;
  std::string_view lib_leaf0;
  std::string_view lib_leaf1;
  std::string_view lib_top;
};

CompilationUnit* ParseTwoLeafTop(SourceManager& mgr, Arena& arena,
                                 DiagEngine& diag,
                                 const BindLeafParams& params) {
  std::string src;
  src += "module leaf; endmodule\n";
  src += "module leaf; endmodule\n";
  src += "module top; leaf u(); endmodule\n";
  src += params.config_body;
  auto fid = mgr.AddFile("<test>", std::move(src));
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  cu->modules[0]->library = params.lib_leaf0;
  cu->modules[1]->library = params.lib_leaf1;
  cu->modules[2]->library = params.lib_top;
  for (auto* cfg : cu->configs) cfg->library = params.lib_top;
  return cu;
}

RtlirModule* BindLeafUnderTop(SourceManager& mgr, Arena& arena,
                              DiagEngine& diag, const BindLeafParams& params) {
  auto* cu = ParseTwoLeafTop(mgr, arena, diag, params);
  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  if (design == nullptr || design->top_modules.empty()) return nullptr;
  auto* top = design->top_modules[0];
  if (top->children.empty()) return nullptr;
  return top->children[0].resolved;
}

TEST(ConfigLiblistClause, UnselectedLiblistFallsBackToParentLibrary) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound =
      BindLeafUnderTop(mgr, arena, diag,
                       BindLeafParams{"config c; design top; endconfig\n",
                                      "libX", "libY", "libY"});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "libY");
}

TEST(ConfigLiblistClause, ParentLibraryFallbackTracksParent) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound =
      BindLeafUnderTop(mgr, arena, diag,
                       BindLeafParams{"config c; design top; endconfig\n",
                                      "libX", "libY", "libX"});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "libX");
}

TEST(ConfigLiblistClause, EmptyDefaultLiblistFallsBackToParentLibrary) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindLeafUnderTop(
      mgr, arena, diag,
      BindLeafParams{"config c; design top; default liblist; endconfig\n",
                     "libX", "libY", "libY"});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "libY");
}

TEST(ConfigLiblistClause, ParentLibraryLackingTheCellLeavesItUnbound) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound =
      BindLeafUnderTop(mgr, arena, diag,
                       BindLeafParams{"config c; design top; endconfig\n",
                                      "libA", "libB", "libZ"});
  EXPECT_EQ(bound, nullptr);
  EXPECT_TRUE(ReportedError(diag.Diagnostics(),
                            "unknown module 'leaf': the configuration's "
                            "parent cell's library (libZ) holds no cell 'leaf' "
                            "for instance 'top.u'",
                            3, "33.4.1.5"));
}

TEST(ConfigLiblistClause, EmptyInstanceLiblistMeansTheParentsLibrary) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindLeafUnderTop(
      mgr, arena, diag,
      BindLeafParams{"config c; design top; default liblist L2 L1;\n"
                     "  instance top.u liblist; endconfig\n",
                     "L1", "L2", "L1"});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "L1");
}

TEST(ConfigLiblistClause, EmptyCellLiblistMeansTheParentsLibrary) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindLeafUnderTop(
      mgr, arena, diag,
      BindLeafParams{"config c; design top; default liblist L2 L1;\n"
                     "  cell leaf liblist; endconfig\n",
                     "L1", "L2", "L1"});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "L1");
}

RtlirDesign* ElaborateCellListDesign(SourceManager& mgr, Arena& arena,
                                     DiagEngine& diag,
                                     const std::string& body) {
  std::string src =
      "module m; endmodule\n"
      "module m; endmodule\n"
      "module adder; m f1(); endmodule\n"
      "module adder; m f1(); endmodule\n"
      "module top; adder a1(); endmodule\n"
      "config c; design rtlLib.top;\n" +
      body + "endconfig\n";
  auto fid = mgr.AddFile("<test>", std::move(src));
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  const std::string_view kLibs[] = {"gateLib", "aLib", "gateLib", "aLib",
                                    "rtlLib"};
  for (size_t i = 0; i < cu->modules.size(); ++i) {
    cu->modules[i]->library = kLibs[i];
  }
  for (auto* cfg : cu->configs) cfg->library = "rtlLib";
  Elaborator elab(arena, diag, cu);
  return elab.Elaborate(cu->configs[0]);
}

TEST(ConfigLiblistClause, CellClauseListIsInheritedByTheCellsSubinstances) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* design = ElaborateCellListDesign(
      mgr, arena, diag,
      "  default liblist gateLib rtlLib;\n  cell adder liblist aLib;\n");
  ASSERT_NE(design, nullptr);
  const RtlirModule* a1 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(a1->library, "aLib");
  ASSERT_FALSE(a1->children.empty());
  ASSERT_NE(a1->children[0].resolved, nullptr);
  EXPECT_EQ(a1->children[0].resolved->library, "aLib");
}

TEST(ConfigLiblistClause, LiblistExcludingAnInterfaceLeavesItUnbound) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  std::string src =
      "interface ifc; endinterface\n"
      "module top; ifc i(); endmodule\n"
      "config c; design libA.top; instance top.i liblist libA; endconfig\n";
  auto fid = mgr.AddFile("<test>", std::move(src));
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  cu->interfaces[0]->library = "libB";
  cu->modules[0]->library = "libA";
  cu->configs[0]->library = "libA";
  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  const bool kBound = design != nullptr && !design->top_modules.empty() &&
                      !design->top_modules[0]->children.empty() &&
                      design->top_modules[0]->children[0].resolved != nullptr;
  EXPECT_FALSE(kBound);
  EXPECT_TRUE(ReportedError(diag.Diagnostics(),
                            "unknown module 'ifc': the configuration's library "
                            "list (libA) holds no cell 'ifc' for instance "
                            "'top.i'",
                            2, "33.4.1.5"));
}

TEST(ConfigLiblistClause, NoParentLibraryContextSkipsFallback) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound =
      BindLeafUnderTop(mgr, arena, diag,
                       BindLeafParams{"config c; design top; endconfig\n",
                                      "libA", "libB", std::string_view{}});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "leaf");
}

TEST(ConfigLiblistClause, CellClauseSelectsLibraryListForCell) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindLeafUnderTop(
      mgr, arena, diag,
      BindLeafParams{
          "config c; design top; cell leaf liblist libB; endconfig\n", "libA",
          "libB", "libC"});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "libB");
}

TEST(ConfigLiblistClause, SelectedListSearchedInOrderFirstWins) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindLeafUnderTop(
      mgr, arena, diag,
      BindLeafParams{
          "config c; design top; cell leaf liblist libA libB; endconfig\n",
          "libA", "libB", "libC"});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "libA");
}

TEST(ConfigLiblistClause, SelectedListOrderDrivesPrecedence) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindLeafUnderTop(
      mgr, arena, diag,
      BindLeafParams{
          "config c; design top; cell leaf liblist libB libA; endconfig\n",
          "libA", "libB", "libC"});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "libB");
}

TEST(ConfigLiblistClause, SelectedListSkipsLibraryWithoutCell) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindLeafUnderTop(
      mgr, arena, diag,
      BindLeafParams{
          "config c; design top; cell leaf liblist libX libB; endconfig\n",
          "libA", "libB", "libC"});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "libB");
}

TEST(ConfigLiblistClause, DefaultSelectedListSearchedInOrder) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindLeafUnderTop(
      mgr, arena, diag,
      BindLeafParams{
          "config c; design top; default liblist libA libB; endconfig\n",
          "libB", "libA", "libC"});
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "libA");
}

TEST(ConfigLiblistClause, LiblistInheritedBySubhierarchy) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>",
                         "module leaf; endmodule\n"
                         "module leaf; endmodule\n"
                         "module mid; leaf u(); endmodule\n"
                         "module mid; leaf u(); endmodule\n"
                         "module top; mid m1(); mid m2(); endmodule\n"
                         "config c; design top; default liblist libR; "
                         "instance top.m1 liblist libB; endconfig\n");
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 5u);
  cu->modules[0]->library = "libB";
  cu->modules[1]->library = "libR";
  cu->modules[2]->library = "libB";
  cu->modules[3]->library = "libR";
  cu->modules[4]->library = "libR";
  for (auto* cfg : cu->configs) cfg->library = "libR";

  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 2u);

  auto* mid1 = top->children[0].resolved;
  ASSERT_NE(mid1, nullptr);
  EXPECT_EQ(mid1->library, "libB");
  ASSERT_EQ(mid1->children.size(), 1u);
  auto* leaf1 = mid1->children[0].resolved;
  ASSERT_NE(leaf1, nullptr);
  EXPECT_EQ(leaf1->library, "libB");

  auto* mid2 = top->children[1].resolved;
  ASSERT_NE(mid2, nullptr);
  EXPECT_EQ(mid2->library, "libR");
  ASSERT_EQ(mid2->children.size(), 1u);
  auto* leaf2 = mid2->children[0].resolved;
  ASSERT_NE(leaf2, nullptr);
  EXPECT_EQ(leaf2->library, "libR");
}

TEST(ConfigLiblistClause, ListHoldingNoCellReportsTheList) {
  auto diags = ConfigElaborationReports(
      "module adder; endmodule\n"
      "module top; adder a1(); endmodule\n"
      "config cfg; design work.top; instance top.a1 liblist gateLib; "
      "endconfig\n");
  EXPECT_TRUE(ReportedError(
      diags,
      "library list (gateLib) holds no cell 'adder' for instance 'top.a1'", 2,
      "33.4.1.5"));
}

RtlirDesign* ElaborateTwoAdderDesign(
    SourceManager& mgr, Arena& arena, DiagEngine& diag, const std::string& body,
    const std::array<std::string_view, 7>& libs) {
  std::string src =
      "module leaf; endmodule\n"
      "module leaf; endmodule\n"
      "module m; leaf u(); endmodule\n"
      "module m; leaf u(); endmodule\n"
      "module adder; m f1(); endmodule\n"
      "module adder; m f1(); endmodule\n"
      "module top; adder a1(); adder a2(); endmodule\n"
      "config c; design rtlLib.top;\n" +
      body + "endconfig\n";
  auto fid = mgr.AddFile("<test>", std::move(src));
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  for (size_t i = 0; i < cu->modules.size(); ++i) {
    cu->modules[i]->library = libs[i];
  }
  for (auto* cfg : cu->configs) cfg->library = "rtlLib";
  Elaborator elab(arena, diag, cu);
  return elab.Elaborate(cu->configs[0]);
}

constexpr std::array<std::string_view, 7> kGateThenALib{
    "gateLib", "aLib", "gateLib", "aLib", "gateLib", "aLib", "rtlLib"};

const RtlirModule* BoundM(const RtlirDesign* design, size_t adder) {
  if (design == nullptr || design->top_modules.empty()) return nullptr;
  const auto& adders = design->top_modules[0]->children;
  if (adders.size() <= adder || adders[adder].resolved == nullptr) {
    return nullptr;
  }
  const auto& ms = adders[adder].resolved->children;
  return ms.empty() ? nullptr : ms[0].resolved;
}

TEST(ConfigLiblistClause, ACellClauseReplacesAListInheritedFromAnInstance) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* design = ElaborateTwoAdderDesign(mgr, arena, diag,
                                         "  default liblist gateLib rtlLib;\n"
                                         "  instance top.a2 liblist aLib;\n"
                                         "  cell m liblist gateLib;\n",
                                         kGateThenALib);
  ASSERT_NE(design, nullptr);
  ASSERT_NE(design->top_modules[0]->children[1].resolved, nullptr);
  EXPECT_EQ(design->top_modules[0]->children[1].resolved->library, "aLib");
  ASSERT_NE(BoundM(design, 1), nullptr);
  EXPECT_EQ(BoundM(design, 1)->library, "gateLib");
  ASSERT_NE(BoundM(design, 0), nullptr);
  EXPECT_EQ(BoundM(design, 0)->library, "gateLib");
}

TEST(ConfigLiblistClause,
     AnInstanceClauseNamingTheInstanceOutranksACellClause) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* design = ElaborateTwoAdderDesign(mgr, arena, diag,
                                         "  default liblist gateLib rtlLib;\n"
                                         "  instance top.a2.f1 liblist aLib;\n"
                                         "  cell m liblist gateLib;\n",
                                         kGateThenALib);
  ASSERT_NE(BoundM(design, 1), nullptr);
  EXPECT_EQ(BoundM(design, 1)->library, "aLib");
}

TEST(ConfigLiblistClause, ACellClauseListUnderAnInstanceClauseIsInherited) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* design = ElaborateTwoAdderDesign(mgr, arena, diag,
                                         "  default liblist gateLib rtlLib;\n"
                                         "  instance top.a2 liblist aLib;\n"
                                         "  cell m liblist gateLib;\n",
                                         kGateThenALib);
  const RtlirModule* m = BoundM(design, 1);
  ASSERT_NE(m, nullptr);
  ASSERT_FALSE(m->children.empty());
  ASSERT_NE(m->children[0].resolved, nullptr);
  EXPECT_EQ(m->children[0].resolved->library, "gateLib");
}

TEST(ConfigLiblistClause, ACellClauseListHoldingNoCellUnderAnInstanceReports) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  ElaborateTwoAdderDesign(
      mgr, arena, diag,
      "  default liblist gateLib rtlLib;\n"
      "  instance top.a1 liblist aLib;\n"
      "  cell m liblist gateLib;\n",
      {{"gateLib", "aLib", "otherLib", "aLib", "gateLib", "aLib", "rtlLib"}});
  EXPECT_TRUE(ReportedError(diag.Diagnostics(),
                            "unknown module 'm': the configuration's library "
                            "list (gateLib) holds no cell 'm' for instance "
                            "'top.a1.f1'",
                            6, "33.4.1.5"));
}

RtlirDesign* ElaborateTwoPrimitiveDesign(
    SourceManager& mgr, Arena& arena, DiagEngine& diag, const std::string& rest,
    std::initializer_list<std::string_view> module_libs) {
  auto fid = mgr.AddFile(
      "<test>",
      "primitive p(output y, input a); table 0 : 0 ; 1 : 1 ; endtable "
      "endprimitive\n"
      "primitive p(output y, input a); table 0 : 1 ; 1 : 0 ; endtable "
      "endprimitive\n" +
          rest);
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  cu->udps[0]->library = "rtlLib";
  cu->udps[1]->library = "gateLib";
  auto lib = module_libs.begin();
  for (auto* mod : cu->modules) mod->library = *lib++;
  for (auto* cfg : cu->configs) cfg->library = "rtlLib";
  Elaborator elab(arena, diag, cu);
  return elab.Elaborate(cu->configs[0]);
}

TEST(ConfigLiblistClause, ACellClauseOnAPrimitiveSelectsItsList) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* design = ElaborateTwoPrimitiveDesign(
      mgr, arena, diag,
      "module top; wire y, a; p u(y, a); endmodule\n"
      "config c; design rtlLib.top; default liblist rtlLib gateLib;\n"
      "  cell p liblist gateLib; endconfig\n",
      {"rtlLib"});
  ASSERT_NE(design, nullptr);
  const RtlirModule* top = design->top_modules[0];
  ASSERT_EQ(top->udp_insts.size(), 1u);
  EXPECT_EQ(top->udp_insts[0].decl->library, "gateLib");
}

TEST(ConfigLiblistClause, APrimitiveInheritsTheListACellClauseGaveItsParent) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* design = ElaborateTwoPrimitiveDesign(
      mgr, arena, diag,
      "module wrap; wire y, a; p u(y, a); endmodule\n"
      "module top; wrap w(); endmodule\n"
      "config c; design rtlLib.top; default liblist rtlLib gateLib;\n"
      "  cell wrap liblist gateLib; endconfig\n",
      {"gateLib", "rtlLib"});
  ASSERT_NE(design, nullptr);
  const auto& children = design->top_modules[0]->children;
  ASSERT_EQ(children.size(), 1u);
  const RtlirModule* wrap = children[0].resolved;
  ASSERT_NE(wrap, nullptr);
  ASSERT_EQ(wrap->udp_insts.size(), 1u);
  EXPECT_EQ(wrap->udp_insts[0].decl->library, "gateLib");
}

}  // namespace
