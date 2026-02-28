// §10.9.2: Structure assignment patterns

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// 16. Array of structs with assignment pattern.
TEST(ParserSection7, Sec7_2_2_ArrayOfStructsPattern) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } pair_t;\n"
              "  pair_t arr[2];\n"
              "  initial begin\n"
              "    arr[0] = '{1, 2};\n"
              "    arr[1] = '{3, 4};\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
