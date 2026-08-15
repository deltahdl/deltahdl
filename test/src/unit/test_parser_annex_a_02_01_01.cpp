#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {}

TEST(ParameterDeclParsing, ParameterExplicitType) {
  auto r = Parse("module m; parameter int WIDTH = 8; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_FALSE(item->is_localparam);
  EXPECT_EQ(item->name, "WIDTH");
}

TEST(ParameterDeclParsing, ParameterImplicitType) {
  auto r = Parse("module m; parameter SIZE = 16; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
}

TEST(ParameterDeclParsing, ParameterPackedDim) {
  auto r = Parse("module m; parameter [31:0] ADDR = 0; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
}

TEST(ParameterDeclParsing, ListOfParamAssignments) {
  auto r = Parse("module m; parameter int A = 1, B = 2, C = 3; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int param_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) param_count++;
  }
  EXPECT_GE(param_count, 3);
}

TEST(ParameterDeclParsing, ParamAssignmentNoDefault) {
  auto r = Parse("module m #(parameter int P)(); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterDeclParsing, LocalparamSignedType) {
  auto r = Parse("module m; localparam signed [3:0] N = 4'sb1111; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
}

TEST(ParameterDeclParsing, ParameterExpressionDefault) {
  auto r = Parse("module m; parameter int HALF = 16 / 2; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "HALF");
}

TEST(ParameterDeclParsing, ErrorParameterMissingSemicolon) {
  auto r = Parse("module m; parameter int X = 5 endmodule");
  // TokenKindName renders every keyword as `token`, so the 'endmodule' standing
  // where the ';' belongs is not named; §6.20.1 and the line carry the rest.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got token", 1, "6.20.1"));
}

TEST(ParameterDeclParsing, ErrorLocalparamMissingSemicolon) {
  auto r = Parse("module m; localparam int Y = 10 endmodule");
  // A localparam declaration runs through the same list terminator as a
  // parameter one, so §6.20.1 is where its missing ';' is filed.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got token", 1, "6.20.1"));
}

TEST(ParameterDeclParsing, ErrorParameterMissingEquals) {
  auto r = Parse("module m; parameter int X; endmodule");
  EXPECT_TRUE(ReportedError(
      r.diags, "parameter declaration requires a default value", 1, "6.20.1"));
}

TEST(ParameterDeclParsing, ErrorLocalparamMissingEquals) {
  auto r = Parse("module m; localparam int Y; endmodule");
  EXPECT_TRUE(ReportedError(
      r.diags, "parameter declaration requires a default value", 1, "6.20.1"));
}

TEST(FormalSyntaxParsing, ParamDecl) {
  auto r = Parse(
      "module m;\n"
      "  parameter int WIDTH = 16;\n"
      "  localparam int DEPTH = 32;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(r.cu->modules[0]->items[1]->kind, ModuleItemKind::kParamDecl);
}

TEST(ParameterDeclParsing, ParameterTypeDecl) {
  auto r = Parse("module m; parameter type T = int; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_FALSE(item->is_localparam);
  EXPECT_EQ(item->name, "T");
}

TEST(ParameterDeclParsing, LocalparamTypeDecl) {
  auto r = Parse("module m; localparam type T = int; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_TRUE(item->is_localparam);
  EXPECT_EQ(item->name, "T");
}

TEST(ParameterDeclParsing, TypeParamForwardEnum) {
  auto r = Parse("module m; parameter type enum T = my_enum_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "T");
}

TEST(ParameterDeclParsing, TypeParamForwardInterfaceClass) {
  auto r =
      Parse("module m; parameter type interface class T = my_ic_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "T");
}

TEST(ParameterDeclParsing, ErrorTypeParamWithoutDefault) {
  auto r = Parse("module m; parameter type T; endmodule");
  EXPECT_TRUE(ReportedError(r.diags,
                            "type parameter 'T' outside a parameter port list "
                            "must have a default type",
                            1, "6.20.1"));
}

TEST(ParameterDeclParsing, ErrorSpecparamMissingSemicolon) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    specparam tpd = 1.5\n"
      "  endspecify\n"
      "endmodule");
  // §6.20.5 owns specparam_declaration, so its list terminator is demanded
  // there. TokenKindName renders 'endspecify' as `token`.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got token", 4, "6.20.5"));
}

TEST(ParameterDeclParsing, TypeParamCommaSeparatedList) {
  auto r = Parse("module m; parameter type T1 = int, T2 = real; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  size_t param_count = 0;
  for (auto* it : r.cu->modules[0]->items) {
    if (it->kind == ModuleItemKind::kParamDecl) ++param_count;
  }
  EXPECT_GE(param_count, 2u);
}

TEST(ParameterDeclParsing, SpecparamDeclaration) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    specparam tpd = 1.5;\n"
      "  endspecify\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterDeclParsing, SpecparamWithPackedDimension) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    specparam [7:0] DELAY = 8'd5;\n"
      "  endspecify\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterDeclParsing, SpecparamListOfAssignments) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    specparam t1 = 1.0, t2 = 2.0;\n"
      "  endspecify\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
