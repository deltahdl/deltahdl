#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DeclarationRangeParsing, AssocDimElaboratesWildcard) {
  ElabFixture f;
  auto* design = Elaborate("module m; int aa [*]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_assoc);
}

TEST(DeclarationRangeParsing, WildcardIndexWidth32) {
  ElabFixture f;
  auto* design = Elaborate("module m; int aa [*]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_EQ(v.assoc_index_width, 32u);
}

TEST(DeclarationRangeParsing, WildcardNotStringIndex) {
  ElabFixture f;
  auto* design = Elaborate("module m; int aa [*]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_FALSE(v.is_string_index);
}

// §7.8.1 — a wildcard-indexed associative array may not be used in a foreach
// loop.
TEST(WildcardIndexType, ForeachOnWildcardIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  initial foreach (aa[i]) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// Contrast: a foreach over a non-wildcard array elaborates cleanly, confirming
// the prohibition is specific to the wildcard index type.
TEST(WildcardIndexType, ForeachOnFixedArrayIsAllowed) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int arr[4];\n"
      "  initial foreach (arr[i]) ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §7.8.1 — an array-locator method that returns index values (find_index) is
// not allowed on a wildcard-indexed associative array.
TEST(WildcardIndexType, FindIndexOnWildcardIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  int idx[$];\n"
      "  initial idx = aa.find_index with (item > 0);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.8.1 — find_first_index also returns indices and is rejected on a wildcard
// associative array.
TEST(WildcardIndexType, FindFirstIndexOnWildcardIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  int idx[$];\n"
      "  initial idx = aa.find_first_index with (item > 0);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.8.1 — likewise find_last_index is rejected on a wildcard associative
// array.
TEST(WildcardIndexType, FindLastIndexOnWildcardIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  int idx[$];\n"
      "  initial idx = aa.find_last_index with (item > 0);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.8.1 — a nonintegral index value is illegal; a real-literal index on a
// wildcard array is rejected.
TEST(WildcardIndexType, NonintegralIndexIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  initial aa[1.5] = 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.8.1 — the nonintegral prohibition also covers a real-typed variable used
// as the index, not just a real literal.
TEST(WildcardIndexType, RealVariableIndexIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  real r;\n"
      "  initial aa[r] = 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.8.1 — the nonintegral prohibition covers every real-valued type. A
// shortreal-typed variable used as the index is rejected.
TEST(WildcardIndexType, ShortrealVariableIndexIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  shortreal sr;\n"
      "  initial aa[sr] = 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.8.1 — likewise a realtime-typed variable is nonintegral and rejected as a
// wildcard index.
TEST(WildcardIndexType, RealtimeVariableIndexIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  realtime rt;\n"
      "  initial aa[rt] = 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.8.1 — unique_index returns an array of index values, so like the other
// index-returning locators it is not allowed on a wildcard associative array.
TEST(WildcardIndexType, UniqueIndexOnWildcardIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  int idx[$];\n"
      "  initial idx = aa.unique_index with (item > 0);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// Contrast: an integral index on the same wildcard array elaborates cleanly.
TEST(WildcardIndexType, IntegralIndexIsAllowed) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  initial aa[3] = 0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
