#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DollarConstantElaboration, DollarBodyParameterSetsUnboundedFlag) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter P = $;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "P") {
      found = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DollarConstantElaboration, DollarPortListParameterSetsUnboundedFlag) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m #(parameter int P = $);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "P") {
      found = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DollarConstantElaboration, BoundedParameterNotUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter P = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  for (auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_FALSE(p.is_unbounded);
    }
  }
}

TEST(DollarConstantElaboration, DollarParameterNotResolved) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter P = $;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  for (auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_FALSE(p.is_resolved);
    }
  }
}

}  // namespace
