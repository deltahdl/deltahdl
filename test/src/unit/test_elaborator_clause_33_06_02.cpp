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

// §33.6.2: "The default liblist statement overrides the library search
// order in the lib.map file; therefore, aLib is always searched before
// rtlLib."  With the lib.map order set as [rtlLib, aLib, gateLib], a
// config carrying `default liblist aLib rtlLib` must flip the binding
// of m to aLib.m even though rtlLib comes first in the map order.
TEST(DefaultLiblistOverride, OverridesLibMapSearchOrder) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseSrc(mgr, arena, diag,
                      "module m;\n"
                      "  parameter int VIEW = 0;\n"
                      "endmodule\n"
                      "module m;\n"
                      "  parameter int VIEW = 1;\n"
                      "endmodule\n"
                      "module m;\n"
                      "  parameter int VIEW = 2;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  m u();\n"
                      "endmodule\n"
                      "config cfg1;\n"
                      "  design top;\n"
                      "  default liblist aLib rtlLib;\n"
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
  // lib.map order would prefer rtlLib.m, but the config's default
  // liblist must take precedence and pick aLib.m.
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "aLib");
}

// §33.6.2: "Because the gateLib library is not included in the liblist,
// the gate-level descriptions of adder and m shall not be used."  When
// a cell exists only in a library that is excluded from the default
// liblist, that cell must not bind — the elaborator should report a
// binding error rather than silently fall back to the excluded library.
TEST(DefaultLiblistOverride, LibrariesNotInLiblistAreExcluded) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseSrc(mgr, arena, diag,
                      "module adder(input wire a, output wire y);\n"
                      "  assign y = ~a;\n"
                      "endmodule\n"
                      "module top(input wire a, output wire y);\n"
                      "  adder u(.a(a), .y(y));\n"
                      "endmodule\n"
                      "config cfg1;\n"
                      "  design top;\n"
                      "  default liblist aLib rtlLib;\n"
                      "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 2u);

  // adder is only available in gateLib, which is excluded from the
  // config's default liblist.
  cu->modules[0]->library = "gateLib";
  cu->modules[1]->library = "rtlLib";

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  elab.Elaborate(cu->configs[0]);
  EXPECT_TRUE(diag.HasErrors());
}

// §33.6.2: "This shall cause the gate representation always to be taken
// before the rtl representation."  Within the default liblist, earlier
// libraries take precedence over later ones — putting gateLib first
// flips the adder/m bindings to the gate views.
TEST(DefaultLiblistOverride, OrderWithinLiblistIsSearchPrecedence) {
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
                      "module top(input wire a, output wire y);\n"
                      "  adder u(.a(a), .y(y));\n"
                      "endmodule\n"
                      "config cfg2;\n"
                      "  design top;\n"
                      "  default liblist gateLib aLib rtlLib;\n"
                      "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 3u);

  cu->modules[0]->library = "aLib";
  cu->modules[1]->library = "gateLib";
  cu->modules[2]->library = "rtlLib";

  Elaborator elab(arena, diag, cu);
  // No SetLibraryDeclarationOrder — the default liblist itself is the
  // search order being tested.
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

// §33.6.2: "The rtl view of top shall be taken because there is no gate
// representation available."  Even with `default liblist gateLib aLib
// rtlLib`, a cell that does not exist in any earlier library in the
// liblist must fall through to the first library in the liblist that
// does contain it — top exists only in rtlLib, so rtlLib.top wins.
TEST(DefaultLiblistOverride, FallsThroughToFirstLiblistEntryThatHasCell) {
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
                      "module top(input wire a, output wire y);\n"
                      "  adder u(.a(a), .y(y));\n"
                      "endmodule\n"
                      "config cfg2;\n"
                      "  design top;\n"
                      "  default liblist gateLib aLib rtlLib;\n"
                      "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 3u);

  cu->modules[0]->library = "aLib";
  cu->modules[1]->library = "gateLib";
  cu->modules[2]->library = "rtlLib";  // only top lives here

  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  EXPECT_EQ(top->library, "rtlLib");
}

// §33.6.2: a config with no default liblist must leave the lib.map's
// declaration order in effect — the default liblist override only
// applies when the config carries one.  Without the clause, §33.6.1's
// "first library in the lib.map containing the cell wins" still holds.
TEST(DefaultLiblistOverride, NoDefaultClauseLeavesLibMapOrderInEffect) {
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
                      "module top(input wire a, output wire y);\n"
                      "  adder u(.a(a), .y(y));\n"
                      "endmodule\n"
                      "config cfg_no_default;\n"
                      "  design top;\n"
                      "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 3u);

  cu->modules[0]->library = "aLib";
  cu->modules[1]->library = "gateLib";
  cu->modules[2]->library = "rtlLib";

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  // rtlLib has no adder, so the next library in lib.map order (aLib) wins.
  EXPECT_EQ(bound->library, "aLib");
}

// §33.6.2 cfg2: the LRM example places `m` inside `adder`, and asserts
// that "the module definitions for adder and m" come from adder.vg.
// That requires the override to apply transitively at every level of
// instantiation — not just at the design top's direct children.  With
// liblist [gateLib, aLib, rtlLib], top.adder must bind gateLib.adder
// and that adder's nested m must independently bind gateLib.m.
TEST(DefaultLiblistOverride, OverrideAppliesTransitivelyAtNestedInstances) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseSrc(mgr, arena, diag,
                      "module m;\n"
                      "  parameter int VIEW = 0;\n"
                      "endmodule\n"
                      "module m;\n"
                      "  parameter int VIEW = 1;\n"
                      "endmodule\n"
                      "module m;\n"
                      "  parameter int VIEW = 2;\n"
                      "endmodule\n"
                      "module adder;\n"
                      "  m f1();\n"
                      "  m f2();\n"
                      "endmodule\n"
                      "module adder;\n"
                      "  m f1();\n"
                      "  m f2();\n"
                      "endmodule\n"
                      "module top;\n"
                      "  adder a();\n"
                      "endmodule\n"
                      "config cfg2;\n"
                      "  design top;\n"
                      "  default liblist gateLib aLib rtlLib;\n"
                      "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->configs.size(), 1u);
  ASSERT_EQ(cu->modules.size(), 6u);

  // Three views of m (one per library), two views of adder (rtl + gate),
  // and top only in rtlLib — mirroring the §33.6 source layout.
  cu->modules[0]->library = "aLib";     // m from adder.v
  cu->modules[1]->library = "gateLib";  // m from adder.vg
  cu->modules[2]->library = "rtlLib";   // m from top.v
  cu->modules[3]->library = "aLib";     // adder from adder.v
  cu->modules[4]->library = "gateLib";  // adder from adder.vg
  cu->modules[5]->library = "rtlLib";   // top from top.v

  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);

  auto* top = design->top_modules[0];
  EXPECT_EQ(top->library, "rtlLib");
  ASSERT_EQ(top->children.size(), 1u);
  auto* picked_adder = top->children[0].resolved;
  ASSERT_NE(picked_adder, nullptr);
  EXPECT_EQ(picked_adder->library, "gateLib");
  ASSERT_EQ(picked_adder->children.size(), 2u);
  for (const auto& child : picked_adder->children) {
    ASSERT_NE(child.resolved, nullptr);
    EXPECT_EQ(child.resolved->library, "gateLib");
  }
}

}  // namespace
