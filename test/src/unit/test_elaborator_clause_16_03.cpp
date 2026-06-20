#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ImmediateAssertionElaboration, AssertInInitialBlockElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic a;\n"
      "  initial assert(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ImmediateAssertionElaboration, AssumeInAlwaysCombElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic a;\n"
      "  always_comb assume(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ImmediateAssertionElaboration, CoverInAlwaysBlockElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic clk, a;\n"
      "  always @(posedge clk) cover(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ImmediateAssertionElaboration, LabeledAssertElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic a;\n"
      "  initial begin chk: assert(a); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ImmediateAssertionElaboration, ActionBlockWithSeverityTasksElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial assert(c) $info(\"pass\"); else $error(\"fail\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ImmediateAssertionElaboration, DeferredImmediateAssertionElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial begin\n"
      "    assert #0 (c);\n"
      "    assume final (c);\n"
      "    cover #0 (c);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
