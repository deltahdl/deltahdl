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
  src += "module adder;\n";
  src += "endmodule\n";
  src += "module adder;\n";
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

  EXPECT_EQ(a->library, "gateLib");
}

TEST(CommandLineLibrarySearchOrder,
     OverrideNamesOnlyDefinitionsComeFromLibMap) {
  LibraryMap libmap;
  libmap.AddDeclaration(MakeDecl("aLib", {"a.v"}), "/proj");
  libmap.AddDeclaration(MakeDecl("gateLib", {"g.v"}), "/proj");

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

  EXPECT_EQ(a->library, "aLib");
}

}  // namespace
