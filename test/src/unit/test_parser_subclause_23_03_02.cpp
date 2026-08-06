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

// §23.3.2: positional and named connections cannot be mixed, but the three
// named forms may be mixed -- here an explicit .a(a) with a wildcard .*.
TEST(ModuleInstantiationParser,
     WildcardMixedWithExplicitNamedConnectionsParses) {
  auto r = Parse(
      "module top;\n"
      "  logic a, b;\n"
      "  child u0(.a(a), .*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §23.3.2: a named_parameter_assignment list must not name the same parameter
// twice.
TEST(ModuleInstantiationParser, DuplicateNamedParameterAssignmentRejected) {
  auto r = Parse(
      "module child #(parameter int W = 1) ();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.W(1), .W(2)) u0();\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
