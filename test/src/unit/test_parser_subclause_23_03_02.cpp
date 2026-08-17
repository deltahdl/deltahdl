#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ModuleInstantiationParser, MultipleWildcardPortConnectionsRejected) {
  auto r = Parse(
      "module top;\n"
      "  child u0(.*, .*);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            ".* port connection shall appear at most once in a "
                            "port connection list",
                            2, "23.3.2"));
}

TEST(ModuleInstantiationParser,
     MixedPositionalAndNamedPortConnectionsRejected) {
  auto r = Parse(
      "module top;\n"
      "  logic a, b;\n"
      "  child u0(a, .b(b));\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "ordered and named port connections cannot be mixed", 3,
      "23.3.2"));
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

// §23.3.2 requires the port connection list and its parentheses, and this
// parser is not what refuses `child u0;` for want of them. The same two
// identifiers and semicolon spell a data declaration whose type_identifier
// §6.18 says should have been declared first, and telling the two apart takes
// the module names, which the parser does not hold: it never sees the
// declarations of other files, and §23.3.1 lets a module be instantiated above
// its own. So the shape is recorded as the data declaration, flagged, and
// ModuleInstantiationElaboration.PortlessInstanceWithoutParensIsReported in
// test/src/unit/test_elaborator_subclause_23_03_02.cpp asserts the §23.3.2
// report the elaborator then makes about this same source.
TEST(ModuleInstantiationParser,
     PortlessInstanceWithoutParensIsLeftToElaborate) {
  auto r = Parse(
      "module child; endmodule\n"
      "module top;\n"
      "  child u0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[1]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "u0");
  EXPECT_EQ(item->data_type.type_name, "child");
  EXPECT_TRUE(item->type_name_undeclared_at_parse);
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
  // §23.10.2.2 owns the named parameter value assignment, so the report over a
  // repeated parameter name stands there rather than under §23.3.2.
  EXPECT_TRUE(ReportedError(r.diags,
                            "duplicate parameter name 'W' in parameter value "
                            "assignment",
                            4, "23.10.2.2"));
}

// §23.3.2 terminates a module instantiation with a ';'. An instantiation left
// without one is rejected at the token standing where the ';' belongs, and the
// report names §23.3.2 rather than the token it wanted.
TEST(ModuleInstantiation, MalformedInstanceListNames23_3_2) {
  auto r = Parse(
      "module m;\n"
      "  sub u1(a)\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';'", 3, "23.3.2"));
}

}  // namespace
