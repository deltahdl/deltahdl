#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §23.5 defines no preprocessor-specific rule for extern modules; this stage
// only needs to confirm the declaration survives preprocessing and remains a
// parseable extern module. The port syntax is invisible to the preprocessor, so
// one representative pass-through case is sufficient here — the ANSI/non-ANSI/
// parameterized port forms are exercised at the parser stage.
TEST(ExternModulePreprocessing, ExternModule) {
  auto r = ParseWithPreprocessor("extern module m(input logic a);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
}

}  // namespace
