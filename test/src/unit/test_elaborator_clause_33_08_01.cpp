#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/library_map.h"
#include "parser/parser.h"

using namespace delta;

namespace {

CompilationUnit* ParseSrc(SourceManager& mgr, Arena& arena, DiagEngine& diag,
                          std::string src) {
  auto fid = mgr.AddFile("<test>", std::move(src));
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  return parser.Parse();
}

LibraryDecl MakeDecl(std::string_view name,
                     std::initializer_list<std::string_view> paths) {
  LibraryDecl d;
  d.name = name;
  for (auto p : paths) d.file_paths.push_back(p);
  return d;
}

CompilationUnit* ParseAdderFixture(SourceManager& mgr, Arena& arena,
                                   DiagEngine& diag) {
  std::string src;
  src += "module top;\n";
  src += "  adder a();\n";
  src += "endmodule\n";
  src += "module adder;\n";  // aLib adder
  src += "endmodule\n";
  src += "module adder;\n";  // gateLib adder
  src += "endmodule\n";
  auto* cu = ParseSrc(mgr, arena, diag, src);
  if (!cu) return nullptr;
  cu->modules[0]->library = "rtlLib";
  cu->modules[1]->library = "aLib";
  cu->modules[2]->library = "gateLib";
  return cu;
}

RtlirModule* FindChild(RtlirModule* parent, std::string_view inst_name) {
  for (auto& c : parent->children) {
    if (c.inst_name == inst_name) return c.resolved;
  }
  return nullptr;
}

// §33.8.1 sentence 1 — the absence-of-config baseline.  With no -L
// override, ResolveSearchOrder yields the lib.map's declaration order
// verbatim, so the elaborator's default-binding pick lines up with the
// first library that the lib.map declared.  This test fixes the
// pre-override behavior; the next test flips it via -L.
TEST(CommandLineLibrarySearchOrder, EmptyOverrideKeepsLibMapDeclarationOrder) {
  LibraryMap libmap;
  libmap.AddDeclaration(MakeDecl("aLib", {"a.v"}), "/proj");
  libmap.AddDeclaration(MakeDecl("gateLib", {"g.v"}), "/proj");
  ASSERT_EQ(libmap.LibraryDeclarationOrder().size(), 2u);
  EXPECT_EQ(libmap.LibraryDeclarationOrder()[0], "aLib");
  EXPECT_EQ(libmap.LibraryDeclarationOrder()[1], "gateLib");

  auto effective = libmap.ResolveSearchOrder({});
  ASSERT_EQ(effective.size(), 2u);
  EXPECT_EQ(effective[0], "aLib");
  EXPECT_EQ(effective[1], "gateLib");

  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseAdderFixture(mgr, arena, diag);
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder(std::move(effective));
  auto* design = elab.Elaborate("top");
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);

  auto* a = FindChild(design->top_modules[0], "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->library, "aLib");
}

// §33.8.1 normative SHALL — a non-empty CLI search order overrides the
// default order from the library map file.  Same lib.map and same
// fixture as the empty-override test; only the -L list changes.  The
// flip from aLib to gateLib at the same instance proves the production
// override path actually replaces the lib.map's order rather than
// merging or appending to it.
TEST(CommandLineLibrarySearchOrder, CliOverrideReplacesLibMapDeclarationOrder) {
  LibraryMap libmap;
  libmap.AddDeclaration(MakeDecl("aLib", {"a.v"}), "/proj");
  libmap.AddDeclaration(MakeDecl("gateLib", {"g.v"}), "/proj");

  std::vector<std::string> cli_override = {"gateLib", "aLib"};
  auto effective = libmap.ResolveSearchOrder(cli_override);
  ASSERT_EQ(effective.size(), 2u);
  EXPECT_EQ(effective[0], "gateLib");
  EXPECT_EQ(effective[1], "aLib");

  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseAdderFixture(mgr, arena, diag);
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder(std::move(effective));
  auto* design = elab.Elaborate("top");
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);

  auto* a = FindChild(design->top_modules[0], "a");
  ASSERT_NE(a, nullptr);
  // Same lib.map declared aLib first; only -L changed, and the bind
  // followed -L.  That is what "overrides the default order from the
  // library map file" requires of the production code.
  EXPECT_EQ(a->library, "gateLib");
}

// §33.8.1 sentence 2 — the override carries library names only, with
// the definitions taken from the library map file.  A name on the CLI
// that the lib.map never declared brings no modules of its own; the
// elaborator can still bind the libraries the lib.map does define when
// they appear later in the override.  Naming a phantom library "first"
// here cannot push the bind onto a definition the lib.map never
// supplied.
TEST(CommandLineLibrarySearchOrder, OverrideNamesOnlyDefinitionsComeFromLibMap) {
  LibraryMap libmap;
  libmap.AddDeclaration(MakeDecl("aLib", {"a.v"}), "/proj");
  libmap.AddDeclaration(MakeDecl("gateLib", {"g.v"}), "/proj");

  // "phantomLib" appears in the override but is undefined in the
  // lib.map; aLib follows it so a known library still has a chance to
  // bind.
  std::vector<std::string> cli_override = {"phantomLib", "aLib", "gateLib"};
  auto effective = libmap.ResolveSearchOrder(cli_override);

  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseAdderFixture(mgr, arena, diag);
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder(std::move(effective));
  auto* design = elab.Elaborate("top");
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);

  auto* a = FindChild(design->top_modules[0], "a");
  ASSERT_NE(a, nullptr);
  // phantomLib could not contribute an adder definition because the
  // lib.map does not declare it; the next override entry that the
  // lib.map does define (aLib) wins.
  EXPECT_EQ(a->library, "aLib");
}

}  // namespace
