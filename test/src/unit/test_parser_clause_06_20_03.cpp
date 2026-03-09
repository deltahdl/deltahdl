#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(SourceText, ParamPortTypeParameter) {
  auto r = Parse("module m #(type T = int); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "T");
}

TEST(ParserA24, TypeAssignmentNoDefault) {
  auto r = Parse("module m #(parameter type T); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA24, TypeAssignmentComplexType) {
  auto r = Parse("module m; parameter type T = logic [7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection8, TypeParameterModule) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter type T = int);\n"
              "  T data;\n"
              "endmodule\n"));
}

TEST(ParserSection8, TypeParameterLogicVector) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter type T = logic [7:0]);\n"
              "  T bus;\n"
              "endmodule\n"));
}

TEST(ParserSection6, TypeParamDefaultLogicVector) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter type DATA_T = logic [15:0])\n"
              "  ();\n"
              "  DATA_T data;\n"
              "endmodule\n"));
}

TEST(ParserSection6, TypeParamPort) {
  EXPECT_TRUE(ParseOk6("module top #(type T = real); endmodule\n"));
}

TEST(ParserSection6, LocalparamTypeDecl) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  localparam type testtype = logic;\n"
               "  testtype x;\n"
               "endmodule\n"));
}

TEST(ParserSection6, TypeParameterWithMultipleParams) {
  EXPECT_TRUE(
      ParseOk6("module m #(parameter type T = int, parameter type U = real)\n"
               "  ();\n"
               "  T x;\n"
               "  U y;\n"
               "endmodule\n"));
}

TEST(ParserSection6, TypeParameterDefaultShortint) {
  EXPECT_TRUE(
      ParseOk6("module ma #(parameter p1 = 1, parameter type p2 = shortint)\n"
               "  (input logic [p1:0] i, output logic [p1:0] o);\n"
               "  p2 j = 0;\n"
               "endmodule\n"));
}

TEST(ParserSection6, TypeParamWithForwardType) {
  EXPECT_TRUE(
      ParseOk6("module m #(type enum T = logic);\n"
               "endmodule\n"));
}

TEST(ParserSection6, TypeParamWithStructRestriction) {
  EXPECT_TRUE(
      ParseOk6("module m #(type struct T);\n"
               "endmodule\n"));
}

}  // namespace
