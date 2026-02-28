// §10.9.1: Array assignment patterns

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// § primary — assignment_pattern_expression
TEST(ParserA84, PrimaryAssignmentPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int arr [3] = '{0, 1, 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// pattern ::= '{ pattern { , pattern } }
// pattern ::= '{ member_identifier : pattern { , member_identifier : pattern }
// }
// ---------------------------------------------------------------------------
// §12.6: positional assignment pattern in expression context
TEST(ParserA60701, PatternAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{1, 2, 3};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// assignment_pattern ::= '{ constant_expression { expression { , expression } }
// }
// ---------------------------------------------------------------------------
// §10.9.1: replication form of assignment pattern
TEST(ParserA60701, AssignmentPatternReplication) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{4{8'd0}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §10.9.1: replication form with multiple elements
TEST(ParserA60701, AssignmentPatternReplicationMultiElem) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{2{a, b}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
