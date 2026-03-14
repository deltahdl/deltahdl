#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(OptionalDirectiveExtendedParsing, DefaultTriregStrength) {
  auto r = ParseWithPreprocessor(
      "`default_trireg_strength 50\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

TEST(OptionalDirectiveExtendedParsing, DefaultTriregStrength_CUValue) {
  auto r = ParseWithPreprocessor(
      "`default_trireg_strength 150\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->has_default_trireg_strength);
  EXPECT_EQ(r.cu->default_trireg_strength, 150u);
}

TEST(OptionalDirectiveExtendedParsing, DefaultTriregStrength_NoDirective) {
  auto r = ParseWithPreprocessor("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->has_default_trireg_strength);
}

}  // namespace
