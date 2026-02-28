// §25.3: Interface syntax

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

RtlirDesign* Elaborate(const std::string& src, ElabFixture& f,
                       std::string_view top = "") {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto name = top.empty() ? cu->modules.back()->name : top;
  return elab.Elaborate(name);
}

namespace {

// =============================================================================
// Elaboration tests -- interface instantiation resolved through elaborator
// =============================================================================
// --- Elaborator resolves interface instantiation within a module ---
TEST(ParserAnnexA0412, ElaborationInterfaceInstInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface my_bus(input logic clk, input logic rst);\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk, rst;\n"
      "  my_bus bus0(.clk(clk), .rst(rst));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "my_bus");
  EXPECT_EQ(top->children[0].inst_name, "bus0");
  EXPECT_NE(top->children[0].resolved, nullptr);
}

// --- Elaborator resolves interface inside interface ---
TEST(ParserAnnexA0412, ElaborationInterfaceInsideInterface) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface inner_if(input logic sig);\n"
      "endinterface\n"
      "interface outer_if;\n"
      "  logic sig;\n"
      "  inner_if u0(.sig(sig));\n"
      "endinterface\n"
      "module top;\n"
      "  outer_if oi();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "outer_if");
  auto* outer = top->children[0].resolved;
  ASSERT_NE(outer, nullptr);
  ASSERT_GE(outer->children.size(), 1u);
  EXPECT_EQ(outer->children[0].module_name, "inner_if");
  EXPECT_NE(outer->children[0].resolved, nullptr);
}

}  // namespace
