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

CompilationUnit* ParseCfg4Fixture(SourceManager& mgr, Arena& arena,
                                  DiagEngine& diag,
                                  const std::string& config_text) {
  std::string src;
  src += "module adder;\n";
  src += "  m f1();\n";
  src += "  m f2();\n";
  src += "endmodule\n";
  src += "module adder;\n";
  src += "  m f1();\n";
  src += "  m f2();\n";
  src += "endmodule\n";
  src += "module m;\n";
  src += "endmodule\n";
  src += "module m;\n";
  src += "endmodule\n";
  src += "module m;\n";
  src += "endmodule\n";
  src += "module top;\n";
  src += "  adder a1();\n";
  src += "  adder a2();\n";
  src += "endmodule\n";
  src += config_text;
  auto* cu = ParseSrc(mgr, arena, diag, src);
  if (!cu) return nullptr;

  cu->modules[0]->library = "aLib";
  cu->modules[1]->library = "gateLib";
  cu->modules[2]->library = "aLib";
  cu->modules[3]->library = "gateLib";
  cu->modules[4]->library = "rtlLib";
  cu->modules[5]->library = "rtlLib";
  return cu;
}

RtlirModule* FindChild(RtlirModule* parent, std::string_view inst_name) {
  for (auto& c : parent->children) {
    if (c.inst_name == inst_name) return c.resolved;
  }
  return nullptr;
}

TEST(InstanceClauseLiblistBinding, NamedInstanceUsesItsLiblistOverride) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseCfg4Fixture(mgr, arena, diag,
                              "config cfg4;\n"
                              "  design top;\n"
                              "  default liblist gateLib rtlLib;\n"
                              "  instance top.a2 liblist aLib;\n"
                              "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);

  auto* top = design->top_modules[0];
  EXPECT_EQ(top->library, "rtlLib");
  auto* a1 = FindChild(top, "a1");
  auto* a2 = FindChild(top, "a2");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);

  EXPECT_EQ(a1->library, "gateLib");

  EXPECT_EQ(a2->library, "aLib");
}

TEST(InstanceClauseLiblistBinding, DescendantsInheritLiblistFromInstance) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseCfg4Fixture(mgr, arena, diag,
                              "config cfg4;\n"
                              "  design top;\n"
                              "  default liblist gateLib rtlLib;\n"
                              "  instance top.a2 liblist aLib;\n"
                              "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);

  auto* top = design->top_modules[0];
  auto* a1 = FindChild(top, "a1");
  auto* a2 = FindChild(top, "a2");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  ASSERT_EQ(a1->children.size(), 2u);
  ASSERT_EQ(a2->children.size(), 2u);

  for (const auto& c : a1->children) {
    ASSERT_NE(c.resolved, nullptr);

    EXPECT_EQ(c.resolved->library, "gateLib");
  }
  for (const auto& c : a2->children) {
    ASSERT_NE(c.resolved, nullptr);

    EXPECT_EQ(c.resolved->library, "aLib");
  }
}

TEST(InstanceClauseLiblistBinding, AbsentInstanceClauseLeavesDefaultBinding) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseCfg4Fixture(mgr, arena, diag,
                              "config cfg_no_inst;\n"
                              "  design top;\n"
                              "  default liblist gateLib rtlLib;\n"
                              "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);

  auto* top = design->top_modules[0];
  auto* a1 = FindChild(top, "a1");
  auto* a2 = FindChild(top, "a2");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);

  EXPECT_EQ(a1->library, "gateLib");
  EXPECT_EQ(a2->library, "gateLib");

  for (const auto& c : a2->children) {
    ASSERT_NE(c.resolved, nullptr);
    EXPECT_EQ(c.resolved->library, "gateLib");
  }
}

TEST(InstanceClauseLiblistBinding, OverridesDefaultLiblistExclusion) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseSrc(mgr, arena, diag,
                      "module adder;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  adder a1();\n"
                      "  adder a2();\n"
                      "endmodule\n"
                      "config cfg4_strict;\n"
                      "  design top;\n"
                      "  default liblist gateLib rtlLib;\n"
                      "  instance top.a2 liblist aLib;\n"
                      "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 2u);

  cu->modules[0]->library = "aLib";
  cu->modules[1]->library = "rtlLib";

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);

  auto* top = design->top_modules[0];
  auto* a2 = FindChild(top, "a2");
  ASSERT_NE(a2, nullptr);

  EXPECT_EQ(a2->library, "aLib");
}

}
