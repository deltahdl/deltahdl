

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(ConstExprElab, BodyParameterPromotedWithPortList) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int W = 8);\n"
      "  parameter int MASK = 255;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  bool found = false;
  for (auto& pd : design->top_modules[0]->params) {
    if (pd.name == "MASK") {
      found = true;
      EXPECT_TRUE(pd.is_localparam);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ConstExprElab, PortListParameterDependsOnEarlier) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int N = 4, parameter int N2 = N * 2);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& p = design->top_modules[0]->params[1];
  EXPECT_EQ(p.name, "N2");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 8);
}

TEST(ConstExprElab, NonConstantParamDefaultWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  EXPECT_FALSE(design->top_modules[0]->params[0].is_resolved);
}

}  // namespace
