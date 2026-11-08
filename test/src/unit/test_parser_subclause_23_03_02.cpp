#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(ModuleInstantiationParser, MultipleWildcardPortConnectionsRejected) {
  auto r = Parse(
      "module top;\n"
      "  child u0(.*, .*);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, ".* already appears earlier in this port connection list", 2,
      "23.3.2"));
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

TEST(ModuleInstantiationParser, DuplicateNamedParameterAssignmentRejected) {
  auto r = Parse(
      "module child #(parameter int W = 1) ();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.W(1), .W(2)) u0();\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "duplicate parameter name 'W' in parameter value "
                            "assignment",
                            4, "23.10.2.2"));
}

TEST(ModuleInstantiation, MalformedInstanceListNames23_3_2) {
  auto r = Parse(
      "module m;\n"
      "  sub u1(a)\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';'", 3, "23.3.2"));
}

}  // namespace
