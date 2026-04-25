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

// §33.6.1: "all instances of module adder shall use aLib.adder
// (because aLib is the first library specified that contains a cell
// named adder)."  The §33.6 lib.map declares rtlLib first, then aLib,
// then gateLib; rtlLib does not contain adder, so the first library
// in declaration order that does (aLib) wins.
TEST(DefaultLibraryBinding, FirstLibraryContainingCellWinsForAdder) {
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
                      "endmodule\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 3u);

  cu->modules[0]->library = "aLib";
  cu->modules[1]->library = "gateLib";
  cu->modules[2]->library = "rtlLib";

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate("top");
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);

  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "aLib");
}

// §33.6.1: "all instances of module m shall use rtlLib.m (because
// rtlLib is the first library that contains m)."  When the cell
// appears in every library, the very first library in the lib.map's
// declaration order wins.
TEST(DefaultLibraryBinding, FirstLibraryContainingCellWinsForM) {
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
                      "endmodule\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 4u);

  cu->modules[0]->library = "aLib";
  cu->modules[1]->library = "gateLib";
  cu->modules[2]->library = "rtlLib";
  cu->modules[3]->library = "rtlLib";

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate("top");
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);

  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "rtlLib");
}

// §33.6.1: a library that does not contain the cell name is skipped.
// Search order [rtlLib, aLib, gateLib] with adder only in gateLib must
// resolve to gateLib — every earlier library in the order is silently
// passed over.
TEST(DefaultLibraryBinding, EarlierLibrariesWithoutCellAreSkipped) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseSrc(mgr, arena, diag,
                      "module adder(input wire a, output wire y);\n"
                      "  assign y = ~a;\n"
                      "endmodule\n"
                      "module top(input wire a, output wire y);\n"
                      "  adder u(.a(a), .y(y));\n"
                      "endmodule\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 2u);

  cu->modules[0]->library = "gateLib";
  cu->modules[1]->library = "rtlLib";

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate("top");
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);

  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "gateLib");
}

// §33.6.1: the rule is anchored to the lib.map's declaration order;
// reversing the order reverses the binding when a cell appears in
// multiple libraries.  Same source as the adder test above, swapped
// order, opposite result.
TEST(DefaultLibraryBinding, ReversedDeclarationOrderReversesBinding) {
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
                      "endmodule\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 3u);

  cu->modules[0]->library = "aLib";
  cu->modules[1]->library = "gateLib";
  cu->modules[2]->library = "rtlLib";

  Elaborator elab(arena, diag, cu);
  // gateLib first this time — its adder must win.
  elab.SetLibraryDeclarationOrder({"gateLib", "aLib", "rtlLib"});
  auto* design = elab.Elaborate("top");
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);

  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* bound = top->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "gateLib");
}

// §33.6.1 says "all instances of module adder shall use aLib.adder" —
// the rule is uniform across every instance with the same cell name in
// the same scope.  Two sibling instantiations of adder must both
// resolve to the same library cell.
TEST(DefaultLibraryBinding, AllSiblingInstancesPickSameLibrary) {
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
                      "module top(input wire a, output wire y1, y2);\n"
                      "  adder u1(.a(a), .y(y1));\n"
                      "  adder u2(.a(a), .y(y2));\n"
                      "endmodule\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 3u);

  cu->modules[0]->library = "aLib";
  cu->modules[1]->library = "gateLib";
  cu->modules[2]->library = "rtlLib";

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate("top");
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);

  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 2u);
  ASSERT_NE(top->children[0].resolved, nullptr);
  ASSERT_NE(top->children[1].resolved, nullptr);
  EXPECT_EQ(top->children[0].resolved->library, "aLib");
  EXPECT_EQ(top->children[1].resolved->library, "aLib");
}

// §33.6.1: the search rule fires for every instance, including those
// nested inside an already-bound cell.  After top.adder binds to
// aLib.adder, that adder's own instantiation of m must independently
// pick rtlLib.m — the first library in declaration order containing m.
TEST(DefaultLibraryBinding, TransitiveDefaultBindingAtNestedInstance) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseSrc(mgr, arena, diag,
                      "module m;\n"
                      "endmodule\n"
                      "module m;\n"
                      "endmodule\n"
                      "module adder;\n"
                      "  m u_m();\n"
                      "endmodule\n"
                      "module adder;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  adder u_a();\n"
                      "endmodule\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->modules.size(), 5u);

  // m exists in aLib and rtlLib; adder exists in aLib and gateLib;
  // top is in rtlLib.  With order [rtlLib, aLib, gateLib]: top.adder
  // resolves to aLib.adder (rtlLib has no adder) and that adder's m
  // resolves to rtlLib.m (rtlLib does have m, and rtlLib is first).
  cu->modules[0]->library = "aLib";
  cu->modules[1]->library = "rtlLib";
  cu->modules[2]->library = "aLib";
  cu->modules[3]->library = "gateLib";
  cu->modules[4]->library = "rtlLib";

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate("top");
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);

  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* picked_adder = top->children[0].resolved;
  ASSERT_NE(picked_adder, nullptr);
  EXPECT_EQ(picked_adder->library, "aLib");
  ASSERT_EQ(picked_adder->children.size(), 1u);
  auto* picked_m = picked_adder->children[0].resolved;
  ASSERT_NE(picked_m, nullptr);
  EXPECT_EQ(picked_m->library, "rtlLib");
}

}  // namespace
