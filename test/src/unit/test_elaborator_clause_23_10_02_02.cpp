// §23.10.2.2: Parameter value assignment by name

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- Elaborator resolves program with parameters ---
TEST(ParserAnnexA0413, ElaborationProgramInstWithParams) {
  ElabFixture f;
  auto* design = Elaborate(
      "program param_prog #(parameter int W = 8)(input logic [W-1:0] data);\n"
      "endprogram\n"
      "module top;\n"
      "  logic [15:0] d;\n"
      "  param_prog #(.W(16)) u0(.data(d));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "param_prog");
  EXPECT_NE(top->children[0].resolved, nullptr);
}

}  // namespace
