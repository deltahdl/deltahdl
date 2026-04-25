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

// Stage the §33.6 example library structure as a single compilation
// unit: two adder views (aLib, gateLib), three m views (aLib, gateLib,
// rtlLib), and a top in rtlLib that instantiates two adders.  Each
// adder instantiates two m's (f1, f2) so descendant inheritance is
// observable two levels deep.  Ordering of decls matches the library
// labels assigned by the caller.
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
  // adder rtl in aLib, adder gate in gateLib;
  // m rtl in aLib, m gate in gateLib, m rtl in rtlLib;
  // top in rtlLib.
  cu->modules[0]->library = "aLib";
  cu->modules[1]->library = "gateLib";
  cu->modules[2]->library = "aLib";
  cu->modules[3]->library = "gateLib";
  cu->modules[4]->library = "rtlLib";
  cu->modules[5]->library = "rtlLib";
  return cu;
}

// Find the resolved child of `parent` whose inst_name matches.
RtlirModule* FindChild(RtlirModule* parent, std::string_view inst_name) {
  for (auto& c : parent->children) {
    if (c.inst_name == inst_name) return c.resolved;
  }
  return nullptr;
}

// §33.6.4 cfg4 verbatim: the named instance top.a2 picks up its own
// liblist (aLib) while the sibling top.a1 falls through to the
// default liblist (gateLib rtlLib).  This is the headline observation
// of the clause: the instance clause overrides the default for the
// matching path only.
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
  // a1 falls through to the default liblist [gateLib, rtlLib]; gateLib has
  // adder, so a1 binds gateLib.adder.
  EXPECT_EQ(a1->library, "gateLib");
  // a2 picks up the instance liblist [aLib]; aLib has adder, so a2 binds
  // aLib.adder — even though aLib is excluded by the default liblist.
  EXPECT_EQ(a2->library, "aLib");
}

// §33.6.4: "Because the liblist is inherited, all of the descendants
// of top.a2 inherit its liblist from the instance selection clause."
// The two m's inside top.a2 (f1 and f2) must therefore bind from aLib
// even though the m inside top.a1 binds through the default liblist.
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
    // m inside a1 inherits the default [gateLib, rtlLib]; gateLib has m,
    // so it wins.
    EXPECT_EQ(c.resolved->library, "gateLib");
  }
  for (const auto& c : a2->children) {
    ASSERT_NE(c.resolved, nullptr);
    // m inside a2 inherits the instance liblist [aLib], so aLib.m.
    EXPECT_EQ(c.resolved->library, "aLib");
  }
}

// Control: with no instance clause, both subhierarchies follow the
// default liblist.  Removing the instance rule must put a2 (and its
// descendants) back on the default-liblist path.  This anchors the
// instance-clause behavior as the only source of the aLib rebind seen
// in the cfg4 tests.
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
  // Both adders bind through the default liblist now.
  EXPECT_EQ(a1->library, "gateLib");
  EXPECT_EQ(a2->library, "gateLib");
  // And the descendants follow the default too.
  for (const auto& c : a2->children) {
    ASSERT_NE(c.resolved, nullptr);
    EXPECT_EQ(c.resolved->library, "gateLib");
  }
}

// §33.6.4: the instance liblist must override §33.6.2's strict
// default-liblist exclusion for the named path.  In cfg4 the default
// liblist is [gateLib, rtlLib] which excludes aLib; the instance
// clause routes top.a2 to aLib regardless.  Without the override
// taking precedence, no aLib candidate could survive the strict
// filter and a2 would refuse to bind (or wrongly fall back to
// gateLib).  This test confirms the override fires by setting up a
// fixture where aLib is the ONLY library carrying adder (gateLib's
// adder is removed): a2 must still resolve, proving the instance
// liblist replaces — not augments — the default for the matched path.
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

  // adder lives only in aLib — excluded by the default liblist; top in
  // rtlLib so the design statement still resolves.
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
  // The instance liblist [aLib] supplants the default [gateLib, rtlLib]
  // for top.a2 — even though the default would have excluded aLib.
  EXPECT_EQ(a2->library, "aLib");
}

}  // namespace
