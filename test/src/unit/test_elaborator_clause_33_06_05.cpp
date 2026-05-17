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

CompilationUnit* ParseCfg5Fixture(SourceManager& mgr, Arena& arena,
                                  DiagEngine& diag,
                                  const std::string& config_text) {
  std::string src;
  src += "module top;\n";
  src += "  adder a1();\n";
  src += "  adder a2();\n";
  src += "endmodule\n";
  src += "module m;\n";
  src += "endmodule\n";
  src += "module adder;\n";
  src += "  m f1();\n";
  src += "  m f2();\n";
  src += "endmodule\n";
  src += "module m;\n";
  src += "endmodule\n";
  src += "module adder;\n";
  src += "  m f1();\n";
  src += "  m f2();\n";
  src += "endmodule\n";
  src += "module m;\n";
  src += "endmodule\n";
  src += config_text;
  auto* cu = ParseSrc(mgr, arena, diag, src);
  if (!cu) return nullptr;
  cu->modules[0]->library = "rtlLib";
  cu->modules[1]->library = "rtlLib";
  cu->modules[2]->library = "aLib";
  cu->modules[3]->library = "aLib";
  cu->modules[4]->library = "gateLib";
  cu->modules[5]->library = "gateLib";
  return cu;
}

RtlirModule* FindChild(RtlirModule* parent, std::string_view inst_name) {
  for (auto& c : parent->children) {
    if (c.inst_name == inst_name) return c.resolved;
  }
  return nullptr;
}

constexpr const char* kCfg5And6 =
    "config cfg5;\n"
    "  design aLib.adder;\n"
    "  default liblist gateLib aLib;\n"
    "  instance adder.f1 liblist rtlLib;\n"
    "endconfig\n"
    "config cfg6;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "  instance top.a2 use work.cfg5:config;\n"
    "endconfig\n";

TEST(HierarchicalConfigBinding, NamedInstanceUsesInnerConfigDesignStatement) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseCfg5Fixture(mgr, arena, diag, kCfg5And6);
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->configs.size(), 2u);

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});

  auto* design = elab.Elaborate(cu->configs[1]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);

  auto* top = design->top_modules[0];
  EXPECT_EQ(top->library, "rtlLib");
  auto* a2 = FindChild(top, "a2");
  ASSERT_NE(a2, nullptr);

  EXPECT_EQ(a2->library, "aLib");
  EXPECT_EQ(a2->name, "adder");
}

TEST(HierarchicalConfigBinding, InnerInstanceRuleIsRelativeToInnerTop) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseCfg5Fixture(mgr, arena, diag, kCfg5And6);
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[1]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);

  auto* top = design->top_modules[0];
  auto* a2 = FindChild(top, "a2");
  ASSERT_NE(a2, nullptr);
  ASSERT_EQ(a2->children.size(), 2u);
  auto* a2_f1 = FindChild(a2, "f1");
  ASSERT_NE(a2_f1, nullptr);

  EXPECT_EQ(a2_f1->library, "rtlLib");
}

TEST(HierarchicalConfigBinding, InnerDefaultLiblistAppliesToDescendants) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseCfg5Fixture(mgr, arena, diag, kCfg5And6);
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[1]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);

  auto* top = design->top_modules[0];
  auto* a2 = FindChild(top, "a2");
  ASSERT_NE(a2, nullptr);
  auto* a2_f2 = FindChild(a2, "f2");
  ASSERT_NE(a2_f2, nullptr);

  EXPECT_EQ(a2_f2->library, "gateLib");
}

TEST(HierarchicalConfigBinding, NonDelegatedSiblingFollowsOuterDefault) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseCfg5Fixture(mgr, arena, diag, kCfg5And6);
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[1]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);

  auto* top = design->top_modules[0];
  auto* a1 = FindChild(top, "a1");
  ASSERT_NE(a1, nullptr);

  EXPECT_EQ(a1->library, "aLib");
  ASSERT_EQ(a1->children.size(), 2u);
  for (const auto& c : a1->children) {
    ASSERT_NE(c.resolved, nullptr);

    EXPECT_EQ(c.resolved->library, "aLib");
  }
}

TEST(HierarchicalConfigBinding, UnknownInnerConfigEmitsDiagnostic) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseCfg5Fixture(mgr, arena, diag,
                              "config cfg6_bad;\n"
                              "  design rtlLib.top;\n"
                              "  default liblist aLib rtlLib;\n"
                              "  instance top.a2 use work.cfg_missing:config;\n"
                              "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  (void)elab.Elaborate(cu->configs[0]);
  EXPECT_TRUE(diag.HasErrors());
}

TEST(HierarchicalConfigBinding, MultipleDelegatedSubhierarchiesAreIndependent) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseCfg5Fixture(mgr, arena, diag,
                              "config cfg_a;\n"
                              "  design aLib.adder;\n"
                              "  default liblist aLib;\n"
                              "endconfig\n"
                              "config cfg_g;\n"
                              "  design gateLib.adder;\n"
                              "  default liblist gateLib;\n"
                              "endconfig\n"
                              "config cfg6_multi;\n"
                              "  design rtlLib.top;\n"
                              "  default liblist rtlLib;\n"
                              "  instance top.a1 use work.cfg_a:config;\n"
                              "  instance top.a2 use work.cfg_g:config;\n"
                              "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->configs.size(), 3u);

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[2]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);

  auto* top = design->top_modules[0];
  auto* a1 = FindChild(top, "a1");
  auto* a2 = FindChild(top, "a2");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);

  EXPECT_EQ(a1->library, "aLib");
  EXPECT_EQ(a2->library, "gateLib");

  for (const auto& c : a1->children) {
    ASSERT_NE(c.resolved, nullptr);
    EXPECT_EQ(c.resolved->library, "aLib");
  }
  for (const auto& c : a2->children) {
    ASSERT_NE(c.resolved, nullptr);
    EXPECT_EQ(c.resolved->library, "gateLib");
  }
}

}
