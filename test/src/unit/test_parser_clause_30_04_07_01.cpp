#include "fixture_parser.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §30.4.7.1: absence of a + or - polarity operator on a parallel connection
// records unknown polarity (stored as kNone).
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

// §30.4.7.1: same rule applied to a full connection.
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

}  // namespace
