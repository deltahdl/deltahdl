#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(FunctionLifetimePreprocessor, AutomaticFunctionLocalVar) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  function automatic int factorial(int n);\n"
      "    if (n <= 1) return 1;\n"
      "    return n * factorial(n - 1);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_automatic);
}

}  // namespace
