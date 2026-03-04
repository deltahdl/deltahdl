// §13.4.1: Return values and void functions

#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection6, AutomaticFunctionReturnType) {
  // §6.11.1: Function return type is an integral type.
  auto r = ParseWithPreprocessor("module t;\n"
                                 "  function automatic int get_value();\n"
                                 "    return 42;\n"
                                 "  endfunction\n"
                                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

} // namespace
