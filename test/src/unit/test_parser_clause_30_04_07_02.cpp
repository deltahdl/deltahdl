#include "fixture_parser.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §30.4.7.2: `+` prefix on `=>` records positive polarity on a parallel path.
TEST(PositivePolarityParsing, ParallelPathWithPlusOperator) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a + => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kPositive);
}

// §30.4.7.2: `+` prefix on `*>` records positive polarity on a full path.
TEST(PositivePolarityParsing, FullPathWithPlusOperator) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a + *> b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kPositive);
}

// §30.4.7.2: the LRM example `(In1 +=> q)` places `+` adjacent to `=>` with
// no whitespace. The lexer's max-munch rule tokenizes `+=` as a single token,
// so the parser must still recognize this form as positive polarity.
TEST(PositivePolarityParsing, ParallelPathPlusAdjacentToEqGt) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a +=> b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kPositive);
}

// §30.4.7.2: LRM example `(s +*> q)` places `+` adjacent to `*>` with no
// whitespace. `+*` is not a combined lexer token so this path exercises a
// different tokenization than the `+=>` case.
TEST(PositivePolarityParsing, FullPathPlusAdjacentToStarGt) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a +*> b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kPositive);
}

}  // namespace
