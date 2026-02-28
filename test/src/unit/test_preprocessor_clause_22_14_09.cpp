// §22.14.9: IEEE Std 1800-2017 and IEEE Std 1800-2023 keywords

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ============================================================================
// AST-level checks for `begin_keywords
// ============================================================================
TEST(ParserSection22, BeginKeywordsModuleNamePreserved) {
  auto r = ParseWithPreprocessor(
      "`begin_keywords \"1800-2017\"\n"
      "module bar;\n"
      "  logic x;\n"
      "endmodule\n"
      "`end_keywords\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "bar");
}

}  // namespace
