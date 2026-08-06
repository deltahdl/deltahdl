#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DeclarationListParsing, ListOfParamAssignmentsWithDims) {
  auto r = Parse(
      "module m;\n"
      "  parameter int A [2] = '{1, 2}, B [3] = '{3, 4, 5};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) count++;
  }
  EXPECT_GE(count, 2);
}

TEST(DeclarationAssignmentParsing, ParamAssignmentWithUnpackedDim) {
  auto r = Parse("module m; parameter int ARR [3:0] = '{1,2,3,4}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "ARR");
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

TEST(ExpressionParsing, ParamExprLiteralValue) {
  auto r = Parse(
      "module m #(parameter int P = 10);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->params[0].second->kind,
            ExprKind::kIntegerLiteral);
}

TEST(TaskAndFunctionParsing, StringTypeParam) {
  EXPECT_TRUE(
      ParseOk("virtual class Logger#(parameter string PREFIX = \"LOG\");\n"
              "  static task info(string msg);\n"
              "    $display(\"%s: %s\", PREFIX, msg);\n"
              "  endtask\n"
              "endclass\n"));
}

TEST(TaskAndFunctionParsing, ExplicitlyTypedParam) {
  auto r = Parse(
      "virtual class Buffer#(parameter int SIZE = 256);\n"
      "  static function int capacity();\n"
      "    return SIZE;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DataTypeParsing, ParamDecl_ImplicitType) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  localparam [10:0] p = 1 << 5;\n"
               "  localparam logic [10:0] q = 1 << 5;\n"
               "endmodule\n"));
}

TEST(DataTypeParsing, ParamDecl_UnpackedDims) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  parameter logic [31:0] p [3:0] = '{1, 2, 3, 4};\n"
               "endmodule\n"));
}

TEST(DataTypeParsing, UntypedUnrangedParameterParses) {
  auto r = Parse("module m; parameter P = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "P");
}

TEST(DataTypeParsing, RangedUntypedParameterParses) {
  auto r = Parse("module m; parameter [7:0] P = 200; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "P");
}

}  // namespace
