

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(AttributeInstanceElaboration, SingleAttrNoValueResolves) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "(* synthesis *)\n"
      "module m;\n"
      "  logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& m = *design->top_modules[0];
  ASSERT_GE(m.attrs.size(), 1u);
  EXPECT_EQ(m.attrs[0].name, "synthesis");
  const auto kResolvedValue = m.attrs[0].resolved_value;
  ASSERT_TRUE(kResolvedValue.has_value());
  if (!kResolvedValue.has_value()) return;
  EXPECT_EQ(*kResolvedValue, 1);
}

TEST(AttributeInstanceElaboration, AttrSpecConstantExpressionFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "(* depth = 2 + 3 *)\n"
      "module m;\n"
      "  logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& m = *design->top_modules[0];
  ASSERT_GE(m.attrs.size(), 1u);
  EXPECT_EQ(m.attrs[0].name, "depth");
  const auto kResolvedValue = m.attrs[0].resolved_value;
  ASSERT_TRUE(kResolvedValue.has_value());
  if (!kResolvedValue.has_value()) return;
  EXPECT_EQ(*kResolvedValue, 5);
}

TEST(AttributeInstanceElaboration, MultipleAttrSpecsResolveInOrder) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "(* full_case, parallel_case *)\n"
      "module m;\n"
      "  logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& m = *design->top_modules[0];
  ASSERT_GE(m.attrs.size(), 2u);
  EXPECT_EQ(m.attrs[0].name, "full_case");
  EXPECT_EQ(m.attrs[1].name, "parallel_case");
}

TEST(AttributeInstanceElaboration, AttrValueConstantExpressionCrossLink) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter P = 4;\n"
      "  (* weight = (P > 0) ? 8 : 16 *)\n"
      "  logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& m = *design->top_modules[0];

  bool found = false;
  for (auto& v : m.variables) {
    for (auto& a : v.attrs) {
      if (a.name == "weight") {
        found = true;
        const auto kResolvedValue = a.resolved_value;
        ASSERT_TRUE(kResolvedValue.has_value());
        if (!kResolvedValue.has_value()) return;
        EXPECT_EQ(*kResolvedValue, 8);
      }
    }
  }
  EXPECT_TRUE(found);
}

TEST(AttributeInstanceElaboration, AttrStringValueResolves) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "(* tool = \"synplify\" *)\n"
      "module m;\n"
      "  logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& m = *design->top_modules[0];
  ASSERT_GE(m.attrs.size(), 1u);
  EXPECT_EQ(m.attrs[0].name, "tool");
  EXPECT_EQ(m.attrs[0].string_value, "synplify");
}

TEST(AttributeInstanceElaboration, AttrSpecWithoutValueDefaultsToOne) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "(* mark_debug *)\n"
      "module m;\n"
      "  logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& m = *design->top_modules[0];
  ASSERT_GE(m.attrs.size(), 1u);
  EXPECT_EQ(m.attrs[0].name, "mark_debug");
  const auto kResolvedValue = m.attrs[0].resolved_value;
  ASSERT_TRUE(kResolvedValue.has_value());
  if (!kResolvedValue.has_value()) return;
  EXPECT_EQ(*kResolvedValue, 1);
}

TEST(AttributeInstanceElaboration, AttrInstanceListPreservesOrder) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "(* a = 1, b = 2, c = 3 *)\n"
      "module m;\n"
      "  logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& m = *design->top_modules[0];
  ASSERT_GE(m.attrs.size(), 3u);
  EXPECT_EQ(m.attrs[0].name, "a");
  EXPECT_EQ(m.attrs[1].name, "b");
  EXPECT_EQ(m.attrs[2].name, "c");
  const auto kResolvedValue0 = m.attrs[0].resolved_value;
  const auto kResolvedValue1 = m.attrs[1].resolved_value;
  const auto kResolvedValue2 = m.attrs[2].resolved_value;
  ASSERT_TRUE(kResolvedValue0.has_value());
  if (!kResolvedValue0.has_value()) return;
  ASSERT_TRUE(kResolvedValue1.has_value());
  if (!kResolvedValue1.has_value()) return;
  ASSERT_TRUE(kResolvedValue2.has_value());
  if (!kResolvedValue2.has_value()) return;
  EXPECT_EQ(*kResolvedValue0, 1);
  EXPECT_EQ(*kResolvedValue1, 2);
  EXPECT_EQ(*kResolvedValue2, 3);
}

}  // namespace
