// §7.12.5: Array mapping method

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
// --- Test helpers ---
namespace {

// =========================================================================
// §7.12.5: Array mapping method
// =========================================================================
TEST(ParserSection7, ArrayMapMethod) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  initial qi = arr.map with (item + 1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

}  // namespace
