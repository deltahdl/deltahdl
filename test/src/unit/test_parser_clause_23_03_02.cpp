#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ModuleInstantiationParser, MultipleWildcardPortConnectionsRejected) {
  auto r = Parse(
      "module top;\n"
      "  child u0(.*, .*);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleInstantiationParser,
     MixedPositionalAndNamedPortConnectionsRejected) {
  auto r = Parse(
      "module top;\n"
      "  logic a, b;\n"
      "  child u0(a, .b(b));\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleInstantiationParser, NamedParameterValueAssignmentParses) {
  auto r = Parse(
      "module child #(parameter int WIDTH = 4) ();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.WIDTH(16)) u0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleInstantiationParser, OrderedParameterValueAssignmentParses) {
  auto r = Parse(
      "module child #(parameter int A = 1, parameter int B = 2) ();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(10, 20) u0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleInstantiationParser, InstanceArrayWithUnpackedDimensionParses) {
  auto r = Parse(
      "module child(); endmodule\n"
      "module top;\n"
      "  child u0 [3:0] ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleInstantiationParser, PortlessInstanceWithoutParensRejected) {
  auto r = Parse(
      "module child; endmodule\n"
      "module top;\n"
      "  child u0;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
