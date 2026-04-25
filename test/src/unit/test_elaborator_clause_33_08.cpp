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

// Stamp a fixture where adder appears in both aLib and gateLib so that
// the chosen library can change as binding rules change without altering
// any source text.  config_text is appended verbatim so each test can
// supply (or omit) a configuration of its own.
CompilationUnit* ParseAdderFixture(SourceManager& mgr, Arena& arena,
                                   DiagEngine& diag,
                                   const std::string& config_text) {
  std::string src;
  src += "module top;\n";
  src += "  adder a();\n";
  src += "endmodule\n";
  src += "module adder;\n";  // aLib adder
  src += "endmodule\n";
  src += "module adder;\n";  // gateLib adder
  src += "endmodule\n";
  src += config_text;
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

// §33.8 sentence 1: "In the absence of a configuration, it is possible
// to perform basic control of the library searching order when binding a
// design."  The library-mapping order registered via
// SetLibraryDeclarationOrder is what supplies that control: with no
// config in play, it alone decides which adder cell wins.  This anchors
// the precondition for sentence 2 — the bind result here is the rule
// §33.8 promises a config will override.
TEST(LibraryMappingPrecedence, NoConfigBindingFollowsLibraryMappingOrder) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseAdderFixture(mgr, arena, diag, "");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"aLib", "gateLib"});
  auto* design = elab.Elaborate("top");
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);

  auto* top = design->top_modules[0];
  auto* a = FindChild(top, "a");
  ASSERT_NE(a, nullptr);
  // Library-mapping order [aLib, gateLib] picks aLib.adder.  Sentence 2
  // requires this answer to flip when a config is introduced.
  EXPECT_EQ(a->library, "aLib");
  EXPECT_EQ(a->name, "adder");
}

// §33.8 sentence 2: "When a config is used, the config overrides the
// rules specified in this subclause."  Same fixture, same library
// declaration order — only a config is added.  The config's default
// liblist names gateLib first, so top.a now binds gateLib.adder
// instead of the aLib.adder that the no-config path picked.  The flip
// proves the elaborator gives the config precedence over the library
// mapping.
TEST(LibraryMappingPrecedence, ConfigDefaultLiblistOverridesLibraryMapping) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseAdderFixture(mgr, arena, diag,
                               "config cfg;\n"
                               "  design rtlLib.top;\n"
                               "  default liblist gateLib aLib;\n"
                               "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->configs.size(), 1u);

  Elaborator elab(arena, diag, cu);
  // Identical mapping order to the no-config test — only the config is
  // new.  If the config did not override, this would still bind aLib.
  elab.SetLibraryDeclarationOrder({"aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);

  auto* top = design->top_modules[0];
  auto* a = FindChild(top, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->library, "gateLib");
  EXPECT_EQ(a->name, "adder");
}

}  // namespace
