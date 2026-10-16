#include <gtest/gtest.h>

#include <array>
#include <cstddef>
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

// Bundles the per-call inputs for BindLeafUnderTop so the helper stays under
// the parameter-count threshold.
struct BindLeafParams {
  const std::string& config_body;
  std::string_view lib_leaf0;
  std::string_view lib_leaf1;
  std::string_view lib_top;
};

// Parses the fixed two-leaf/one-top source plus the supplied config body,
// assigns the three modules their libraries, and returns the parsed unit.
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
  // §33.4.1.1: the config compiles with its top module.
  for (auto* cfg : cu->configs) cfg->library = params.lib_top;
  return cu;
}

// Elaborates `config c` (whose body is supplied) over two same-named `leaf`
// cells and a `top` that instantiates one `leaf`, assigning the three modules
// the given libraries, and returns the cell bound to top.u (or nullptr).
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

// §33.4.1.5: when no liblist clause is selected for an unbound instance, the
// effective library list holds only the parent cell's library, so the child
// binds from the library that contains its parent.
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

// Companion: moving the parent into a different library moves the child binding
// with it, confirming the fallback tracks the parent cell.
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

// §33.4.1.5: an empty selected library list is equivalent to none being
// selected, so the parent cell's library is searched.
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

// §33.4.1.5: with no list selected, the list is the parent's library alone, so
// a cell no other library than libA and libB holds is not found under a top
// in libZ.
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

// §33.4.1.5: an instance clause's liblist that names no library selects the
// empty list, which leaves the parent's library, L1, rather than the default
// clause's L2 first.
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

// §33.4.1.5: a cell clause's empty liblist is the same empty list, and so the
// parent's library, L1.
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

// The design of §33.6 reduced to what one cell clause decides: `m` is held by
// gateLib and aLib, `adder`, which instantiates `m`, by gateLib and aLib, and
// `top` by rtlLib. Elaborated under `config c` with `body` as its rules.
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

// §33.4.1.5: a list is inherited downward as instances are bound, whichever
// clause selected it, so the aLib a cell clause gives `adder` is the list its
// `m` is bound from as well: aLib.m, not the default list's gateLib.m.
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

// §33.4.1.5: a selected list is the whole of the search, so an interface held
// only by libB is not found through an instance clause listing libA.
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

// §33.4.1.5: with no parent library context (an unlibraried top cell), the
// parent fallback does not apply and binding proceeds normally.
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

// §33.4.1.4 + §33.4.1.5: a cell selection clause can name the library list to
// search for that cell, restricting the cell's binding to that list.
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

// §33.4.1.5: a selected library list is searched in the order given, so the
// first listed library that defines the cell wins. Here `leaf` exists in both
// libA and libB; listing libA first selects libA.
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

// Companion: reversing the list order changes the winner, confirming the list
// order (not the declaration order) drives the search precedence.
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

// §33.4.1.5: searching the list in order passes over a listed library that
// does not define the cell and binds in the next listed library that does.
// Here `leaf` exists in libA and libB; the list names libX (no leaf) then libB,
// so libX is skipped and libB wins (and unlisted libA is excluded).
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

// §33.4.1.5: a library list selected by the default clause is searched in the
// order the libraries are listed, exercising the default (global library-order)
// resolution path rather than the cell/instance override path. `leaf` is
// declared first in libB and second in libA, yet `default liblist libA libB`
// lists libA first, so top.u binds the libA copy -- proving the list order, not
// the declaration order, decides the winner on the default path.
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

// §33.6.4: a liblist clause on an instance clause governs that instance's own
// cell binding and is inherited by its whole subhierarchy, every descendant
// taking its liblist from the instance selection clause, while a sibling
// instance with no such clause falls back to the default liblist. Here `top`
// instantiates two `mid` cells and `mid`/`leaf` each exist in both libB and
// libR. With `default liblist libR` and `instance top.m1 liblist libB`, the m1
// subtree (mid and its leaf) binds entirely from libB and the m2 subtree binds
// entirely from libR. The earlier form of this test forced
// `instance top.m liblist libB` while placing `mid` only in a third library, so
// the instance's own cell could not bind at all -- which is correct behavior,
// not the inheritance the test meant to check.
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
  cu->modules[0]->library = "libB";  // leaf
  cu->modules[1]->library = "libR";  // leaf
  cu->modules[2]->library = "libB";  // mid
  cu->modules[3]->library = "libR";  // mid
  cu->modules[4]->library = "libR";  // top
  for (auto* cfg : cu->configs) cfg->library = "libR";

  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 2u);

  // top.m1: the instance liblist libB governs m1 and is inherited by its leaf.
  auto* mid1 = top->children[0].resolved;
  ASSERT_NE(mid1, nullptr);
  EXPECT_EQ(mid1->library, "libB");
  ASSERT_EQ(mid1->children.size(), 1u);
  auto* leaf1 = mid1->children[0].resolved;
  ASSERT_NE(leaf1, nullptr);
  EXPECT_EQ(leaf1->library, "libB");

  // top.m2: no instance clause, so the default liblist libR governs the
  // subtree.
  auto* mid2 = top->children[1].resolved;
  ASSERT_NE(mid2, nullptr);
  EXPECT_EQ(mid2->library, "libR");
  ASSERT_EQ(mid2->children.size(), 1u);
  auto* leaf2 = mid2->children[0].resolved;
  ASSERT_NE(leaf2, nullptr);
  EXPECT_EQ(leaf2->library, "libR");
}

// §33.4.1.5 (printed page 939): the libraries listed are searched in the order
// listed for the instance a liblist clause selects. A list holding no cell of
// the instantiated name leaves the instance unbound because of the clause, and
// the report names the list rather than only the module, which work holds.
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

// `top` instantiates `adder` as a1 and a2, `adder` instantiates `m` as f1, and
// `m` instantiates `leaf` as u. Each of leaf, m and adder is declared twice and
// `top` once, the seven modules taking `libs` in that order, and the design is
// elaborated under `config c` with `body` as its rules.
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

// Every leaf, m and adder in gateLib first and aLib second, top in rtlLib.
constexpr std::array<std::string_view, 7> kGateThenALib{
    "gateLib", "aLib", "gateLib", "aLib", "gateLib", "aLib", "rtlLib"};

// The cell bound at `top.<adder>.f1`, or nullptr.
const RtlirModule* BoundM(const RtlirDesign* design, size_t adder) {
  if (design == nullptr || design->top_modules.empty()) return nullptr;
  const auto& adders = design->top_modules[0]->children;
  if (adders.size() <= adder || adders[adder].resolved == nullptr) {
    return nullptr;
  }
  const auto& ms = adders[adder].resolved->children;
  return ms.empty() ? nullptr : ms[0].resolved;
}

// §33.4.1.4 has a cell clause select every instance bound to its cell, and
// §33.4.1.5 has the selection clauses choose the current list, so the cell
// clause on m replaces the aLib list top.a2.f1 would inherit from the instance
// clause on top.a2: gateLib.m. top.a1.f1 binds gateLib.m under the default
// list either way.
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

// §33.4.1.3: an instance clause naming top.a2.f1 itself selects that instance
// specifically, so its aLib list stands ahead of the cell clause on m.
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

// §33.4.1.5: the list the cell clause selected for top.a2.f1 is what its own
// subinstance inherits, being the nearer of the two above it: gateLib.leaf,
// not the aLib.leaf of the instance clause on top.a2.
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

// With m held by otherLib and aLib, the cell clause's gateLib list holds no m
// for top.a1.f1, which the instance clause on top.a1 would have bound out of
// aLib, and the report names the list that was searched.
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

}  // namespace
