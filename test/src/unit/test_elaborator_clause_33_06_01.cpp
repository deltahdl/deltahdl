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

// Parses the two-cell "adder" + "top" design used by several binding tests and
// assigns the standard aLib/gateLib/rtlLib libraries to its three modules.
CompilationUnit* ParseAdderDesign(SourceManager& mgr, Arena& arena,
                                  DiagEngine& diag) {
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
  EXPECT_NE(cu, nullptr);
  EXPECT_FALSE(diag.HasErrors());
  EXPECT_EQ(cu->modules.size(), 3u);
  if (cu != nullptr && cu->modules.size() == 3u) {
    cu->modules[0]->library = "aLib";
    cu->modules[1]->library = "gateLib";
    cu->modules[2]->library = "rtlLib";
  }
  return cu;
}

// Elaborates "top" under the given library declaration order and returns the
// library that the sole child of the top module was bound to.
std::string ElaborateAndBoundLibrary(Arena& arena, DiagEngine& diag,
                                     CompilationUnit* cu,
                                     std::vector<std::string> order) {
  Elaborator elab(arena, diag, cu);
  elab.SetLibraryDeclarationOrder(std::move(order));
  auto* design = elab.Elaborate("top");
  EXPECT_FALSE(diag.HasErrors());
  EXPECT_NE(design, nullptr);
  if (design == nullptr || design->top_modules.empty()) {
    return std::string();
  }
  auto* top = design->top_modules[0];
  EXPECT_EQ(top->children.size(), 1u);
  if (top->children.empty()) {
    return std::string();
  }
  auto* bound = top->children[0].resolved;
  EXPECT_NE(bound, nullptr);
  if (bound == nullptr) {
    return std::string();
  }
  return std::string(bound->library);
}

TEST(DefaultLibraryBinding, FirstLibraryContainingCellWinsForAdder) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseAdderDesign(mgr, arena, diag);
  ASSERT_NE(cu, nullptr);

  std::string bound =
      ElaborateAndBoundLibrary(arena, diag, cu, {"rtlLib", "aLib", "gateLib"});
  EXPECT_EQ(bound, "aLib");
}

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

  std::string bound =
      ElaborateAndBoundLibrary(arena, diag, cu, {"rtlLib", "aLib", "gateLib"});
  EXPECT_EQ(bound, "rtlLib");
}

TEST(DefaultLibraryBinding, ReversedDeclarationOrderReversesBinding) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseAdderDesign(mgr, arena, diag);
  ASSERT_NE(cu, nullptr);

  std::string bound =
      ElaborateAndBoundLibrary(arena, diag, cu, {"gateLib", "aLib", "rtlLib"});
  EXPECT_EQ(bound, "gateLib");
}

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
