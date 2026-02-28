// §23.10.1: defparam statement


#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- Defparam tests ---
TEST(Elaboration, Defparam_OverridesDefault) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter WIDTH = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.WIDTH = 16;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  auto* child = mod->children[0].resolved;
  ASSERT_NE(child, nullptr);
  ASSERT_EQ(child->params.size(), 1);
}

TEST(Elaboration, Defparam_OverridesDefault_Value) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter WIDTH = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.WIDTH = 16;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* child = design->top_modules[0]->children[0].resolved;
  EXPECT_EQ(child->params[0].resolved_value, 16);
  EXPECT_TRUE(child->params[0].is_resolved);
}

TEST(Elaboration, Defparam_NotFoundWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter WIDTH = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.BOGUS = 99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

}  // namespace
