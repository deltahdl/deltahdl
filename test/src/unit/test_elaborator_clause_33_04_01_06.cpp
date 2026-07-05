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

// Bundles the elaboration context and the three module libraries so the
// BindOnlyChild helper stays under the parameter-count threshold.
struct BindOnlyChildArgs {
  SourceManager& mgr;
  Arena& arena;
  DiagEngine& diag;
  const std::string& src;
  std::string_view lib0;
  std::string_view lib1;
  std::string_view lib2;
};

// Parses the source and assigns the three modules' libraries to lib0/lib1/lib2.
CompilationUnit* ParseWithLibraries(const BindOnlyChildArgs& args) {
  auto fid = args.mgr.AddFile("<test>", args.src);
  Lexer lex(args.mgr.FileContent(fid), fid, args.diag);
  Parser parser(lex, args.arena, args.diag);
  auto* cu = parser.Parse();
  cu->modules[0]->library = args.lib0;
  cu->modules[1]->library = args.lib1;
  cu->modules[2]->library = args.lib2;
  return cu;
}

// Parses and config-elaborates the given source (three modules whose libraries
// are set to lib0/lib1/lib2), returning the cell bound to the single child of
// the design's top module.
RtlirModule* BindOnlyChild(const BindOnlyChildArgs& args) {
  auto* cu = ParseWithLibraries(args);
  Elaborator elab(args.arena, args.diag, cu);
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
  auto* bound = BindOnlyChild(
      {mgr, arena, diag, kSubUsesWidget, "mainLib", "otherLib", "mainLib"});
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
  auto* bound = BindOnlyChild(
      {mgr, arena, diag, kSubUsesWidget, "mainLib", "otherLib", "otherLib"});
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

// §33.4.1.6: the optional ':config' suffix on a use clause selects a like-named
// configuration explicitly, rather than a plain module of the same name. Here a
// module 'bot' exists (in lib1) and a configuration 'bot' is also declared; the
// outer config's clause 'use lib1.bot:config' must bind through the
// configuration, so the configuration's own rules govern bot's subtree. Config
// 'bot' pins its child leaf to libB via its default liblist, while the outer
// config's default liblist is libA -- observing libB on the grandchild proves
// the configuration (not the bare module) was the thing selected by ':config'.
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
  cu->modules[0]->library = "libA";    // leaf
  cu->modules[1]->library = "libB";    // leaf
  cu->modules[2]->library = "lib1";    // bot
  cu->modules[3]->library = "libTop";  // top

  // Elaborate the outer config `c` (configs[0]); its use clause delegates top.b
  // to config `bot` (configs[1]) because of the :config suffix.
  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);

  // top.b binds to the use target's cell, module lib1.bot.
  auto* bot = top->children[0].resolved;
  ASSERT_NE(bot, nullptr);
  EXPECT_EQ(bot->name, "bot");
  EXPECT_EQ(bot->library, "lib1");

  // The selected configuration's default liblist (libB) governs bot's subtree,
  // so its leaf binds from libB rather than the outer config's default libA --
  // only reachable if `:config` selected config `bot` over the module `bot`.
  ASSERT_EQ(bot->children.size(), 1u);
  auto* leaf = bot->children[0].resolved;
  ASSERT_NE(leaf, nullptr);
  EXPECT_EQ(leaf->library, "libB");
}

// §33.4.1.6: a use clause on an instance selection binds that exact instance to
// the named library.cell. Here `widget` exists in both libA and libB and the
// parent `top` is in a third library, so ordinary resolution would take the
// first-declared libA copy; the clause `instance top.u use libB.widget` instead
// pins top.u to the libB copy.
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
  cu->modules[0]->library = "libA";    // widget
  cu->modules[1]->library = "libB";    // widget
  cu->modules[2]->library = "libTop";  // top

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

// §33.4.1.6: when the instance use clause omits the library, the library is
// inherited from the parent cell. `top` (in libP) instantiates a `foo`, but the
// clause `instance top.u use bar` rebinds it to `bar`; with no library named,
// bar is sought in top's own library, libP -- and the rebinding makes the bound
// cell name (bar) differ from the instance's declared name (foo).
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
  cu->modules[0]->library = "libP";  // bar
  cu->modules[1]->library = "libP";  // foo
  cu->modules[2]->library = "libP";  // top

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

}  // namespace
