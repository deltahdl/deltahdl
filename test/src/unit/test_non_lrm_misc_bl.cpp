// Non-LRM tests

#include "fixture_parser.h"
#include "elaborator/type_eval.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §6.7.1: Supply0 with range.
TEST(ParserSection6, Sec6_7_1_Supply0WithRange) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  supply0 [3:0] gnd_bus;\n"
              "endmodule\n"));
}

// §6.7.1: Supply1 with range.
TEST(ParserSection6, Sec6_7_1_Supply1WithRange) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  supply1 [3:0] vdd_bus;\n"
              "endmodule\n"));
}

}  // namespace
