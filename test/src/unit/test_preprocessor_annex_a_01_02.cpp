// Annex A.1.2: SystemVerilog source text

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.1.2 description — all alternatives
// =============================================================================
// description: module_declaration
TEST(SourceText, DescriptionModule) {
  auto r = ParseWithPreprocessor("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

}  // namespace
