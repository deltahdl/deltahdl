#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabClause09_02_02, FourAlwaysVariantsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  always #5 clk = ~clk;\n"
      "  always_comb a = b & c;\n"
      "  always_latch if (clk) b = a;\n"
      "  always_ff @(posedge clk) c <= a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());

  bool has_always = false, has_comb = false;
  bool has_latch = false, has_ff = false;
  for (auto& p : design->top_modules[0]->processes) {
    switch (p.kind) {
      case RtlirProcessKind::kAlways:
        has_always = true;
        break;
      case RtlirProcessKind::kAlwaysComb:
        has_comb = true;
        break;
      case RtlirProcessKind::kAlwaysLatch:
        has_latch = true;
        break;
      case RtlirProcessKind::kAlwaysFF:
        has_ff = true;
        break;
      default:
        break;
    }
  }
  EXPECT_TRUE(has_always);
  EXPECT_TRUE(has_comb);
  EXPECT_TRUE(has_latch);
  EXPECT_TRUE(has_ff);
}

TEST(ElabClause09_02_02, MultipleAlwaysCombElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  always_comb a = b;\n"
      "  always_comb c = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());

  int comb_count = 0;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysComb) ++comb_count;
  }
  EXPECT_EQ(comb_count, 2);
}

}  // namespace
