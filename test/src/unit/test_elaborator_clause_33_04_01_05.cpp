#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
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
  return cu;
}

// Elaborates `config c` (whose body is supplied) over two same-named `leaf`
// cells and a `top` that instantiates one `leaf`, assigning the three modules
// the given libraries, and returns the cell bound to top.u (or nullptr).
RtlirModule* BindLeafUnderTop(SourceManager& mgr, Arena& arena,
                              DiagEngine& diag, const std::string& config_body,
                              std::string_view lib_leaf0,
                              std::string_view lib_leaf1,
                              std::string_view lib_top) {
  auto* cu = ParseTwoLeafTop(
      mgr, arena, diag,
      BindLeafParams{config_body, lib_leaf0, lib_leaf1, lib_top});
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
      BindLeafUnderTop(mgr, arena, diag, "config c; design top; endconfig\n",
                       "libX", "libY", "libY");
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
      BindLeafUnderTop(mgr, arena, diag, "config c; design top; endconfig\n",
                       "libX", "libY", "libX");
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
      mgr, arena, diag, "config c; design top; default liblist; endconfig\n",
      "libX", "libY", "libY");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "libY");
}

// §33.4.1.5: when the parent's library does not contain the cell, the parent
// fallback yields nothing and resolution continues with the remaining cells.
TEST(ConfigLiblistClause, ParentFallbackSkippedWhenParentLacksCell) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound =
      BindLeafUnderTop(mgr, arena, diag, "config c; design top; endconfig\n",
                       "libA", "libB", "libZ");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "leaf");
  EXPECT_EQ(bound->library, "libA");
}

// §33.4.1.5: with no parent library context (an unlibraried top cell), the
// parent fallback does not apply and binding proceeds normally.
TEST(ConfigLiblistClause, NoParentLibraryContextSkipsFallback) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound =
      BindLeafUnderTop(mgr, arena, diag, "config c; design top; endconfig\n",
                       "libA", "libB", std::string_view{});
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
      "config c; design top; cell leaf liblist libB; endconfig\n", "libA",
      "libB", "libC");
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
      "config c; design top; cell leaf liblist libA libB; endconfig\n", "libA",
      "libB", "libC");
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
      "config c; design top; cell leaf liblist libB libA; endconfig\n", "libA",
      "libB", "libC");
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
      "config c; design top; cell leaf liblist libX libB; endconfig\n", "libA",
      "libB", "libC");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "libB");
}

// §33.4.1.5: a liblist clause is inherited hierarchically downward, so it
// governs cells bound anywhere below the instance it names.
TEST(ConfigLiblistClause, LiblistInheritedBySubhierarchy) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile(
      "<test>",
      "module leaf; endmodule\n"
      "module leaf; endmodule\n"
      "module mid; leaf u(); endmodule\n"
      "module top; mid m(); endmodule\n"
      "config c; design top; instance top.m liblist libB; endconfig\n");
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 4u);
  cu->modules[0]->library = "libA";
  cu->modules[1]->library = "libB";
  cu->modules[2]->library = "libC";
  cu->modules[3]->library = "libC";

  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_NE(design, nullptr);
  auto* mid = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(mid, nullptr);
  ASSERT_EQ(mid->children.size(), 1u);
  auto* leaf = mid->children[0].resolved;
  ASSERT_NE(leaf, nullptr);
  EXPECT_EQ(leaf->library, "libB");
}

}  // namespace
