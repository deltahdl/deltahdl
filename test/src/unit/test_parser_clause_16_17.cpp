// §16.17: Expect statement

#include "fixture_parser.h"

using namespace delta;

  return nullptr;
}

namespace {

// =============================================================================
// §A.2.10 Production #2: concurrent_assertion_statement
// concurrent_assertion_statement ::=
//     assert_property_statement | assume_property_statement
//   | cover_property_statement  | cover_sequence_statement
//   | restrict_property_statement
// =============================================================================
// Productions #3-#5 tested above (assert/assume/cover property).
// =============================================================================
// §A.2.10 Production #6: expect_property_statement
// expect_property_statement ::= expect ( property_spec ) action_block
// =============================================================================
TEST(ParserA210, ExpectPropertyStatement) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  initial begin\n"
      "    expect (a |-> b) $display(\"pass\"); else $display(\"fail\");\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserA210, ExpectPropertyStatement_NoActions) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    expect (req |-> ack);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
