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

CompilationUnit* ParseAdderFixture(SourceManager& mgr, Arena& arena,
                                   DiagEngine& diag,
                                   const std::string& config_text) {
  std::string src;
  src += "module top;\n";
  src += "  adder a();\n";
  src += "endmodule\n";
  src += "module adder;\n";
  src += "endmodule\n";
  src += "module adder;\n";
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

  EXPECT_EQ(a->library, "aLib");
  EXPECT_EQ(a->name, "adder");
}

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

}
