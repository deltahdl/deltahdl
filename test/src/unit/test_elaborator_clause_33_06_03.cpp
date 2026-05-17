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

  cu->modules[0]->library = "aLib";
  cu->modules[1]->library = "gateLib";
  cu->modules[2]->library = "aLib";
  cu->modules[3]->library = "gateLib";
  cu->modules[4]->library = "rtlLib";
  cu->modules[5]->library = "rtlLib";

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

  EXPECT_EQ(picked_adder->library, "aLib");

  EXPECT_EQ(picked_m->library, "gateLib");
}

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

  cu->modules[0]->library = "aLib";
  cu->modules[1]->library = "gateLib";
  cu->modules[2]->library = "rtlLib";
  cu->modules[3]->library = "aLib";
  cu->modules[4]->library = "gateLib";
  cu->modules[5]->library = "rtlLib";

  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder({"rtlLib", "aLib", "gateLib"});
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);

  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* picked_adder = top->children[0].resolved;
  ASSERT_NE(picked_adder, nullptr);

  EXPECT_EQ(picked_adder->library, "aLib");
  ASSERT_EQ(picked_adder->children.size(), 1u);
  auto* nested_m = picked_adder->children[0].resolved;
  ASSERT_NE(nested_m, nullptr);

  EXPECT_EQ(nested_m->library, "gateLib");
}

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

  EXPECT_EQ(bound->library, "aLib");
}

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

}
