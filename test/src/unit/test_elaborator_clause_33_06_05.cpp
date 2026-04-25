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

// Stage the §33.6 example library structure used by the §33.6.5 worked
// example.  Each adder instantiates two m's (f1, f2) so binding for
// descendants of a delegated instance can be observed two levels deep.
// rtlLib carries top and one m; aLib carries adder and one m; gateLib
// carries the gate-level adder and one m.
CompilationUnit* ParseCfg5Fixture(SourceManager& mgr, Arena& arena,
                                  DiagEngine& diag,
                                  const std::string& config_text) {
  std::string src;
  src += "module top;\n";
  src += "  adder a1();\n";
  src += "  adder a2();\n";
  src += "endmodule\n";
  src += "module m;\n";  // rtlLib m
  src += "endmodule\n";
  src += "module adder;\n";  // aLib adder (rtl)
  src += "  m f1();\n";
  src += "  m f2();\n";
  src += "endmodule\n";
  src += "module m;\n";  // aLib m
  src += "endmodule\n";
  src += "module adder;\n";  // gateLib adder (gate)
  src += "  m f1();\n";
  src += "  m f2();\n";
  src += "endmodule\n";
  src += "module m;\n";  // gateLib m
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

// The two configs from the §33.6.5 worked example.  cfg5 elaborates the
// adder subhierarchy on its own; cfg6 elaborates the full design and
// delegates top.a2 to cfg5.  A test fixture installs both with the
// exact source text from the LRM.
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

// §33.6.5: "The binding clause specifies the work.cfg5:config
// configuration is to be used to resolve the bindings of instance
// top.a2 and its descendants. It is the design statement in config
// cfg5 that defines the exact binding for the top.a2 instance itself."
// cfg5's design statement names aLib.adder, so top.a2 must bind to
// aLib's adder regardless of cfg6's own default liblist ordering.
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
  // cfg6 is the outer config the user runs.
  auto* design = elab.Elaborate(cu->configs[1]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);

  auto* top = design->top_modules[0];
  EXPECT_EQ(top->library, "rtlLib");
  auto* a2 = FindChild(top, "a2");
  ASSERT_NE(a2, nullptr);
  // cfg5 design = aLib.adder → top.a2 binds aLib's adder.
  EXPECT_EQ(a2->library, "aLib");
  EXPECT_EQ(a2->name, "adder");
}

// §33.6.5: "The rest of cfg5 defines the rules to bind the descendants
// of top.a2.  Notice the instance clause in cfg5 is relative to its
// own top-level module, adder."  cfg5 carries an instance rule
// `instance adder.f1 liblist rtlLib;` — that path is relative to
// adder, so it must apply to top.a2.f1 in the outer hierarchy.
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
  // cfg5 maps adder.f1 to rtlLib — that path is rooted at cfg5's own
  // top (adder), so in cfg6's hierarchy the rule binds top.a2.f1.
  EXPECT_EQ(a2_f1->library, "rtlLib");
}

// §33.6.5: the inner config's default liblist supplies the binding for
// any descendant of the delegated instance not picked up by a
// more-specific inner rule.  cfg5's default liblist is `gateLib aLib`,
// so top.a2.f2 (no inner instance rule applies) must bind from
// gateLib first.  Without this rule kicking in, the descendant would
// instead fall back to cfg6's default liblist (aLib rtlLib) and bind
// aLib.m.
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
  // cfg5 default = [gateLib, aLib]; gateLib has m, so f2 binds gateLib.m.
  EXPECT_EQ(a2_f2->library, "gateLib");
}

// §33.6.5: "take the full default aLib adder for the top.a1 instance".
// The non-delegated sibling top.a1 (and its descendants) must follow
// cfg6's own default liblist (aLib rtlLib) — the inner config has no
// reach outside the delegated subhierarchy.  Without the delegation
// being scoped to top.a2, an over-eager translation would also rebind
// top.a1's children.
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
  // cfg6 default = [aLib, rtlLib]; aLib has adder.
  EXPECT_EQ(a1->library, "aLib");
  ASSERT_EQ(a1->children.size(), 2u);
  for (const auto& c : a1->children) {
    ASSERT_NE(c.resolved, nullptr);
    // aLib has m, so descendants of a1 bind aLib.m too.
    EXPECT_EQ(c.resolved->library, "aLib");
  }
}

// §33.6.5: an `instance ... use lib.cfg:config;` clause whose named
// config does not exist in the compilation unit is a binding error —
// the elaborator cannot resolve the delegated subhierarchy without it.
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

// §33.6.5 demonstrates the delegation mechanism with one delegated
// subtree (top.a2 → cfg5).  The same mechanism naturally extends to
// multiple disjoint delegations from a single outer config — each
// delegation binds its own named instance and descendants, with no
// crosstalk between them.  This test pins that property: cfg6_multi
// hands top.a1 to one inner config (forcing aLib for that subtree)
// and top.a2 to another (forcing gateLib), and the outer default
// liblist is set up so that neither library would win on its own.
// Both subtrees must land on the library their inner config picks.
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
  // Each named instance follows the design statement of its own
  // delegated config — cfg_a binds aLib.adder, cfg_g binds gateLib.adder.
  EXPECT_EQ(a1->library, "aLib");
  EXPECT_EQ(a2->library, "gateLib");
  // Descendants of each delegated subtree pick up their own inner
  // default liblist independently.
  for (const auto& c : a1->children) {
    ASSERT_NE(c.resolved, nullptr);
    EXPECT_EQ(c.resolved->library, "aLib");
  }
  for (const auto& c : a2->children) {
    ASSERT_NE(c.resolved, nullptr);
    EXPECT_EQ(c.resolved->library, "gateLib");
  }
}

}  // namespace
