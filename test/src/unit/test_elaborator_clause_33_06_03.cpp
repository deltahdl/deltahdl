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

// §33.6.3 — the cfg3 example from the LRM, with the "selects all"
// claim observed directly: top instantiates m three times, and every
// sibling must rebind to gateLib.m even though the default liblist
// (aLib rtlLib) would have routed m through aLib.  Picking up all
// three siblings is what makes "selects all cells named m" testable;
// a single-instance form would not distinguish "binds the first" from
// "binds every".
TEST(CellClauseBinding, AppliesToAllInstancesOfThatCellName) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseSrc(mgr, arena, diag,
                      "module m;\n"
                      "endmodule\n"
                      "module m;\n"
                      "endmodule\n"
                      "module m;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  m u1();\n"
                      "  m u2();\n"
                      "  m u3();\n"
                      "endmodule\n"
                      "config cfg3;\n"
                      "  design top;\n"
                      "  default liblist aLib rtlLib;\n"
                      "  cell m use gateLib.m;\n"
                      "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 4u);

  cu->modules[0]->library = "aLib";
  cu->modules[1]->library = "gateLib";
  cu->modules[2]->library = "rtlLib";
  cu->modules[3]->library = "rtlLib";

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);

  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 3u);
  for (const auto& child : top->children) {
    ASSERT_NE(child.resolved, nullptr);
    EXPECT_EQ(child.resolved->library, "gateLib");
  }
}

// §33.6.3: the cell clause names a specific cell and only that cell
// reroutes — adder in cfg3's example continues to bind through the
// default liblist (aLib).  The cell-clause override must not leak to
// unrelated cell names.
TEST(CellClauseBinding, DoesNotAffectOtherCellNames) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseSrc(mgr, arena, diag,
                      "module adder(input wire a, output wire y);\n"
                      "  assign y = a;\n"
                      "endmodule\n"
                      "module adder(input wire a, output wire y);\n"
                      "  assign y = ~a;\n"
                      "endmodule\n"
                      "module m;\n"
                      "endmodule\n"
                      "module m;\n"
                      "endmodule\n"
                      "module m;\n"
                      "endmodule\n"
                      "module top(input wire a, output wire y);\n"
                      "  adder u_a(.a(a), .y(y));\n"
                      "  m u_m();\n"
                      "endmodule\n"
                      "config cfg3;\n"
                      "  design top;\n"
                      "  default liblist aLib rtlLib;\n"
                      "  cell m use gateLib.m;\n"
                      "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 6u);

  cu->modules[0]->library = "aLib";     // adder rtl
  cu->modules[1]->library = "gateLib";  // adder gate
  cu->modules[2]->library = "aLib";     // m rtl variant in aLib
  cu->modules[3]->library = "gateLib";  // m gate
  cu->modules[4]->library = "rtlLib";   // m rtl variant in rtlLib
  cu->modules[5]->library = "rtlLib";   // top

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);

  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 2u);

  RtlirModule* picked_adder = nullptr;
  RtlirModule* picked_m = nullptr;
  for (const auto& child : top->children) {
    ASSERT_NE(child.resolved, nullptr);
    if (child.resolved->name == "adder") picked_adder = child.resolved;
    if (child.resolved->name == "m") picked_m = child.resolved;
  }
  ASSERT_NE(picked_adder, nullptr);
  ASSERT_NE(picked_m, nullptr);
  // adder follows the default liblist [aLib, rtlLib]: aLib has adder, so aLib.
  EXPECT_EQ(picked_adder->library, "aLib");
  // m is rerouted by the cell clause regardless of the default liblist.
  EXPECT_EQ(picked_m->library, "gateLib");
}

// §33.6.3: "explicitly binds" — the binding is unconditional.  Even
// when the default liblist excludes gateLib (cfg3's liblist is just
// aLib + rtlLib), the cell clause must still bind m to gateLib.m.
// Without this rule the strict liblist filter from §33.6.2 would
// reject gateLib outright.
TEST(CellClauseBinding, OverridesDefaultLiblistExclusion) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseSrc(mgr, arena, diag,
                      "module m;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  m u();\n"
                      "endmodule\n"
                      "config cfg3;\n"
                      "  design top;\n"
                      "  default liblist aLib rtlLib;\n"
                      "  cell m use gateLib.m;\n"
                      "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 2u);

  // m exists only in gateLib, which is NOT on the default liblist.
  // §33.6.2 alone would refuse to bind it; §33.6.3's cell clause has
  // to override that.
  cu->modules[0]->library = "gateLib";
  cu->modules[1]->library = "rtlLib";

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);

  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "gateLib");
}

// §33.6.3: "selects all cells named m" — the rule is name-scoped over
// the entire elaborated hierarchy, so an m nested several levels deep
// must rebind to gateLib.m the same way a top-level m would.
TEST(CellClauseBinding, AppliesTransitivelyAtNestedInstances) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseSrc(mgr, arena, diag,
                      "module m;\n"
                      "endmodule\n"
                      "module m;\n"
                      "endmodule\n"
                      "module m;\n"
                      "endmodule\n"
                      "module adder;\n"
                      "  m f1();\n"
                      "endmodule\n"
                      "module adder;\n"
                      "  m f1();\n"
                      "endmodule\n"
                      "module top;\n"
                      "  adder u_a();\n"
                      "endmodule\n"
                      "config cfg3;\n"
                      "  design top;\n"
                      "  default liblist aLib rtlLib;\n"
                      "  cell m use gateLib.m;\n"
                      "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 6u);

  cu->modules[0]->library = "aLib";     // m rtl
  cu->modules[1]->library = "gateLib";  // m gate
  cu->modules[2]->library = "rtlLib";   // m rtl
  cu->modules[3]->library = "aLib";     // adder rtl
  cu->modules[4]->library = "gateLib";  // adder gate
  cu->modules[5]->library = "rtlLib";   // top

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);

  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* picked_adder = top->children[0].resolved;
  ASSERT_NE(picked_adder, nullptr);
  // adder picks aLib via the default liblist (aLib has adder, rtlLib does not).
  EXPECT_EQ(picked_adder->library, "aLib");
  ASSERT_EQ(picked_adder->children.size(), 1u);
  auto* nested_m = picked_adder->children[0].resolved;
  ASSERT_NE(nested_m, nullptr);
  // The nested m still rebinds to gateLib.m thanks to the cell clause.
  EXPECT_EQ(nested_m->library, "gateLib");
}

// Control: with no cell clause in the config, default-liblist binding
// from §33.6.2 stays in effect — m falls through to the first liblist
// entry that contains it (aLib here).  This anchors the cell-clause
// behavior as the only source of the gateLib rebind seen above.
TEST(CellClauseBinding, AbsentCellClauseLeavesDefaultBindingInEffect) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseSrc(mgr, arena, diag,
                      "module m;\n"
                      "endmodule\n"
                      "module m;\n"
                      "endmodule\n"
                      "module m;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  m u();\n"
                      "endmodule\n"
                      "config cfg_no_cell;\n"
                      "  design top;\n"
                      "  default liblist aLib rtlLib;\n"
                      "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 4u);

  cu->modules[0]->library = "aLib";
  cu->modules[1]->library = "gateLib";
  cu->modules[2]->library = "rtlLib";
  cu->modules[3]->library = "rtlLib";

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);

  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  // Default liblist [aLib, rtlLib] picks aLib first.
  EXPECT_EQ(bound->library, "aLib");
}

// §33.6.3: the binding is "explicit", so the cell clause must apply
// even when the config carries no default liblist at all.  Without
// the clause the lib.map declaration order [rtlLib, aLib, gateLib]
// would route m through rtlLib (§33.6.1).  With only the cell clause
// — and no default-liblist override beneath it to confound the
// observation — m must still resolve to gateLib.m.
TEST(CellClauseBinding, BindsExplicitlyWithoutDefaultLiblist) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseSrc(mgr, arena, diag,
                      "module m;\n"
                      "endmodule\n"
                      "module m;\n"
                      "endmodule\n"
                      "module m;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  m u();\n"
                      "endmodule\n"
                      "config cfg_cell_only;\n"
                      "  design top;\n"
                      "  cell m use gateLib.m;\n"
                      "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->configs.size(), 1u);
  ASSERT_EQ(cu->modules.size(), 4u);

  cu->modules[0]->library = "aLib";
  cu->modules[1]->library = "gateLib";
  cu->modules[2]->library = "rtlLib";
  cu->modules[3]->library = "rtlLib";

  Elaborator elab(arena, diag, cu);
  // rtlLib leads the lib.map order, so without the cell clause m
  // would have bound to rtlLib.m.  The cell clause is the only
  // binding signal in the config and must redirect m to gateLib.m.
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);

  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "gateLib");
}

}  // namespace
