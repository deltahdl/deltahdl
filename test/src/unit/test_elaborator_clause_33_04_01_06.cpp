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

// Parses and config-elaborates the given source (three modules whose libraries
// are set to lib0/lib1/lib2), returning the cell bound to the single child of
// the design's top module.
RtlirModule* BindOnlyChild(SourceManager& mgr, Arena& arena, DiagEngine& diag,
                           const std::string& src, std::string_view lib0,
                           std::string_view lib1, std::string_view lib2) {
  auto fid = mgr.AddFile("<test>", src);
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  cu->modules[0]->library = lib0;
  cu->modules[1]->library = lib1;
  cu->modules[2]->library = lib2;
  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  EXPECT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  EXPECT_EQ(top->children.size(), 1u);
  return top->children[0].resolved;
}

constexpr const char* kSubUsesWidget =
    "module widget; endmodule\n"
    "module widget; endmodule\n"
    "module top; sub u(); endmodule\n"
    "config c; design top; cell sub use widget; endconfig\n";

// §33.4.1.6: a use clause that omits the library name inherits it from the
// parent cell, so the selected cell binds within the parent's library.
TEST(ConfigUseClause, UseWithoutLibraryInheritsParentLibrary) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindOnlyChild(mgr, arena, diag, kSubUsesWidget, "mainLib",
                              "otherLib", "mainLib");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "widget");
  EXPECT_EQ(bound->library, "mainLib");
}

// Companion: the inherited library follows the parent cell, so relocating the
// parent relocates the use-clause binding.
TEST(ConfigUseClause, InheritedUseLibraryTracksParent) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* bound = BindOnlyChild(mgr, arena, diag, kSubUsesWidget, "mainLib",
                              "otherLib", "otherLib");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->name, "widget");
  EXPECT_EQ(bound->library, "otherLib");
}

// §33.4.1.6: a use clause binds one cell but does not add its library to the
// current library list; a cell present only in that referenced library, but
// not on the search list, stays unbound.
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

  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 2u);
  // The use clause binds w to libB.w2 exactly.
  auto* w_bound = top->children[0].resolved;
  ASSERT_NE(w_bound, nullptr);
  EXPECT_EQ(w_bound->name, "w2");
  EXPECT_EQ(w_bound->library, "libB");
  // But libB never joined the library list, so the libB-only cell is unbound.
  EXPECT_EQ(top->children[1].resolved, nullptr);
}

// §33.4.1.6: a use clause names the exact library and cell to bind; when no
// such cell exists the selected instance is left unbound.
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

  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
}

}  // namespace
