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

  cu->modules[0]->library = "gateLib";
  cu->modules[1]->library = "rtlLib";

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  elab.Elaborate(cu->configs[0]);
  EXPECT_TRUE(diag.HasErrors());
}

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
  cu->modules[2]->library = "rtlLib";

  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  EXPECT_EQ(top->library, "rtlLib");
}

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

  EXPECT_EQ(bound->library, "aLib");
}

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

  cu->modules[0]->library = "aLib";
  cu->modules[1]->library = "gateLib";
  cu->modules[2]->library = "rtlLib";
  cu->modules[3]->library = "aLib";
  cu->modules[4]->library = "gateLib";
  cu->modules[5]->library = "rtlLib";

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

}
