// Non-LRM tests

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

// --- program_instantiation: empty parameter list ---
TEST(ParserAnnexA0413, ProgramInstEmptyParam) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog #() u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_prog");
  EXPECT_TRUE(item->inst_params.empty());
}

// =============================================================================
// Elaboration tests -- program instantiation resolved through elaborator
// =============================================================================
// --- Elaborator resolves program instantiation within a module ---
TEST(ParserAnnexA0413, ElaborationProgramInstInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "program my_prog(input logic clk, input logic rst);\n"
      "endprogram\n"
      "module top;\n"
      "  logic clk, rst;\n"
      "  my_prog p0(.clk(clk), .rst(rst));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "my_prog");
  EXPECT_EQ(top->children[0].inst_name, "p0");
  EXPECT_NE(top->children[0].resolved, nullptr);
}

}  // namespace
