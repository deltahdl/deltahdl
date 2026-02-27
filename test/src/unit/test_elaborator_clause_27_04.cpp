// §27.4: Loop generate constructs


#include "common/types.h"
#include "elaboration/sensitivity.h"
#include "elaboration/type_eval.h"
#include "lexer/token.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- Generate tests ---
TEST(Elaborator, GenerateForCreatesVars) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter N = 3) ();\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      logic [31:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 3u);
  EXPECT_EQ(mod->variables[0].name, "i_0_x");
  EXPECT_EQ(mod->variables[1].name, "i_1_x");
  EXPECT_EQ(mod->variables[2].name, "i_2_x");
}

TEST(Elaborator, GenerateForZeroIterations) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter N = 0) ();\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      logic [31:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 0u);
}

TEST(Elaborator, GenerateForWithAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter N = 2) ();\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      logic [31:0] w;\n"
      "      assign w = 100;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 2u);
  EXPECT_EQ(mod->assigns.size(), 2u);
  EXPECT_EQ(mod->variables[0].name, "i_0_w");
  EXPECT_EQ(mod->variables[1].name, "i_1_w");
}

}  // namespace
