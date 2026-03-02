// §18.6.1: Randomize()

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.8.2 Subroutine calls — randomize_call
// =============================================================================
// § randomize_call ::= randomize { attribute_instance }
//   [ ( [ variable_identifier_list | null ] ) ]
//   [ with [ ( [ identifier_list ] ) ] constraint_block ]
TEST(ParserA82, RandomizeCallBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
