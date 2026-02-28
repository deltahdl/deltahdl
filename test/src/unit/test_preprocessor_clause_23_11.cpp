// §23.11: Binding auxiliary code to scopes or instances

#include "fixture_parser.h"

using namespace delta;

namespace {

// 3. Bind constructs at CU scope (§23.11) — CU scope can also hold bind.
TEST(ParserClause03, Cl3_12_1_CuScopeBindDirective) {
  auto r = ParseWithPreprocessor(
      "module target; endmodule\n"
      "bind target target chk_inst();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "target");
}

}  // namespace
