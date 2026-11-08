#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

uint32_t WidthOfVariable(const RtlirModule* mod, std::string_view name) {
  for (const auto& v : mod->variables) {
    if (v.name == name) return v.width;
  }
  return 0;
}

TEST(DeclarationSectionElaboration, ARangeSizesASpecparamAtEitherSite) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam [7:0] tBody = 5;\n"
      "  specify\n"
      "    specparam [7:0] tSpec = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* mod = design->top_modules[0];
  EXPECT_EQ(WidthOfVariable(mod, "tBody"), 8u);
  EXPECT_EQ(WidthOfVariable(mod, "tSpec"), WidthOfVariable(mod, "tBody"));
}

TEST(DeclarationSectionElaboration,
     AValueSizesARangelessSpecparamAtEitherSite) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam tBody = 4'd5;\n"
      "  specify\n"
      "    specparam tSpec = 4'd5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* mod = design->top_modules[0];
  EXPECT_EQ(WidthOfVariable(mod, "tBody"), 4u);
  EXPECT_EQ(WidthOfVariable(mod, "tSpec"), WidthOfVariable(mod, "tBody"));
}

TEST(DeclarationSectionElaboration, OneRangeGovernsTheWholeAssignmentList) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specify\n"
      "    specparam [3:0] tRise = 1, tFall = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* mod = design->top_modules[0];
  EXPECT_EQ(WidthOfVariable(mod, "tRise"), 4u);
  EXPECT_EQ(WidthOfVariable(mod, "tFall"), 4u);
}

}  // namespace
