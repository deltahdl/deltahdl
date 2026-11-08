#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

size_t AssignCount(const RtlirModule* mod) { return mod->assigns.size(); }

const RtlirModule* ElaborateTop(const std::string& src, ElabFixture& f) {
  auto* design = Elaborate(src, f);
  if (design == nullptr || design->top_modules.empty()) return nullptr;
  return design->top_modules[0];
}

TEST(PrimitiveInstanceElaboration, ScalarTerminalsStillBuildTheWholeArray) {
  ElabFixture f;
  const auto* mod = ElaborateTop(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(mod, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(AssignCount(mod), 4u);
}

TEST(PrimitiveInstanceElaboration, TheRangeBoundsSpanTheInstanceCount) {
  ElabFixture f;
  const auto* mod = ElaborateTop(
      "module m;\n"
      "  wire y, a, b;\n"
      "  nand g[7:3](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(mod, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(AssignCount(mod), 5u);
}

TEST(PrimitiveInstanceElaboration, TheRangeCountsInstancesForEveryGroup) {
  ElabFixture f;
  const auto* mod = ElaborateTop(
      "module m;\n"
      "  wire y, a, en;\n"
      "  bufif1 g[3:0](y, a, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(mod, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(AssignCount(mod), 4u);
}

TEST(PrimitiveInstanceElaboration, APullGateArrayBuildsOnePullPerElement) {
  ElabFixture f;
  const auto* mod = ElaborateTop(
      "module m;\n"
      "  wire y;\n"
      "  pulldown p[2:0](y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(mod, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(AssignCount(mod), 3u);
}

TEST(PrimitiveInstanceElaboration, NoRangeAndAnEqualBoundedRangeAreOneEach) {
  ElabFixture f;
  const auto* mod = ElaborateTop(
      "module m;\n"
      "  wire y, z, a, b;\n"
      "  and g1(y, a, b);\n"
      "  and g2[5:5](z, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(mod, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(AssignCount(mod), 2u);
}

}  // namespace
