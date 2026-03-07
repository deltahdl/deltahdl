#include "fixture_parser.h"

using namespace delta;
namespace {

// §7.9.10: Function with associative array argument parses.
TEST(ParserSection7, FuncWithAssocArrayArg) {
  auto r = Parse(
      "module t;\n"
      "  function void foo(int aa[string]);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §7.9.10: Task with assoc array input and output.
TEST(ParserSection7, TaskWithAssocArrayInOut) {
  auto r = Parse(
      "module t;\n"
      "  task bar(input int a[int], output int b[int]);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
