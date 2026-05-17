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

TEST(ModuleInstantiationParser, MixedPositionalAndNamedPortConnectionsRejected) {
  auto r = Parse(
      "module top;\n"
      "  logic a, b;\n"
      "  child u0(a, .b(b));\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §23.3.2 Syntax 23-6: parameter_value_assignment ::= # ( [ list_of_parameter
// _value_assignments ] ). The BNF must accept the named form using a leading
// `#( .NAME(expr) )` before the instance name.
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

// §23.3.2 Syntax 23-6: parameter_value_assignment with ordered list shall
// parse the positional `#(value, value)` form.
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

// §23.3.2 Syntax 23-6: name_of_instance ::= instance_identifier {
// unpacked_dimension }. An instance array shall parse with `[range]` between
// the identifier and the port-connection list.
TEST(ModuleInstantiationParser, InstanceArrayWithUnpackedDimensionParses) {
  auto r = Parse(
      "module child(); endmodule\n"
      "module top;\n"
      "  child u0 [3:0] ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §23.3.2: "The parentheses shall be required on all module instantiations,
// even when the instantiated module does not have ports." The parser must
// require `()` after the instance identifier.
TEST(ModuleInstantiationParser, PortlessInstanceWithoutParensRejected) {
  auto r = Parse(
      "module child; endmodule\n"
      "module top;\n"
      "  child u0;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
