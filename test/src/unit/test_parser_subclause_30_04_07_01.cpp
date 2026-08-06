#include "fixture_parser.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(UnknownPolarityParsing, ParallelPathWithoutOperator) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kNone);
}

TEST(UnknownPolarityParsing, FullPathWithoutOperator) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a, b *> c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kNone);
}

// §30.4.7.1's discriminator is operator ABSENCE: the unknown classification is
// only correct because the parser reads the '+'/'-' operator and reports its
// absence. The accepting tests above assert kNone, but kNone is also the
// field's default, so they would pass even if the rule were removed. These
// contrast cases pin the boundary: the same parse path, given a polarity
// operator, must report a non-unknown polarity — proving the no-operator result
// is computed, not merely defaulted. The specific positive/negative value is
// §30.4.7.2/.3's claim, so we assert only that it is not unknown.
TEST(UnknownPolarityParsing, ParallelPathWithOperatorIsNotUnknown) {
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
  EXPECT_NE(si->path.polarity, SpecifyPolarity::kNone);
}

TEST(UnknownPolarityParsing, FullPathWithOperatorIsNotUnknown) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a, b -*> c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_NE(si->path.polarity, SpecifyPolarity::kNone);
}

}  // namespace
