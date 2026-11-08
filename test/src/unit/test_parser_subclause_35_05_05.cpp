#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(FunctionDeclParsing, DpiImportFunctionVoid) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void c_print(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

TEST_F(AnnexHParseTest, DpiImportFunctionStringResultAccepted) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" pure function string get_version();\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "get_version");
  EXPECT_EQ(items[0]->return_type.kind, DataTypeKind::kString);
  EXPECT_TRUE(items[0]->dpi_is_pure);
}

TEST(FunctionDeclParsing, DpiImportFunctionImplicitReturnTypeRejected) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function get_value(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "an imported function must explicitly specify a "
                            "data type or void for its result",
                            2, "35.5.5"));
}

TEST(FunctionDeclParsing, DpiImportFunctionChandleResultAccepted) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function chandle make_obj();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kChandle);
}

TEST(FunctionDeclParsing, DpiImportFunctionScalarBitResultAccepted) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function bit read_flag();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kBit);
}

TEST(FunctionDeclParsing, DpiImportFunctionScalarLogicResultAccepted) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function logic read_line();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kLogic);
}

TEST(FunctionDeclParsing, DpiImportFunctionRealResultAccepted) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function real compute();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kReal);
}

TEST(FunctionDeclParsing, DpiImportFunctionPackedLogicResultRejected) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function logic [3:0] read_nibble();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "result type is not permitted for a DPI imported function", 2,
      "35.5.5"));
}

TEST(FunctionDeclParsing, DpiImportFunctionTimeResultRejected) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function time stamp();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "result type is not permitted for a DPI imported function", 2,
      "35.5.5"));
}

TEST(FunctionDeclParsing, DpiImportFunctionPackedBitResultRejected) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function bit [7:0] read_byte();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "result type is not permitted for a DPI imported function", 2,
      "35.5.5"));
}

TEST(FunctionDeclParsing, DpiImportFunctionWidthOnePackedBitResultRejected) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function bit [0:0] read_single();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "result type is not permitted for a DPI imported function", 2,
      "35.5.5"));
}

TEST(FunctionDeclParsing, DpiImportFunctionIntegerResultRejected) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function integer count();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "result type is not permitted for a DPI imported function", 2,
      "35.5.5"));
}

TEST(FunctionDeclParsing, DpiImportFunctionByteResultAccepted) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function byte read_octet();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kByte);
}

TEST(FunctionDeclParsing, DpiImportFunctionShortintResultAccepted) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function shortint read_half();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kShortint);
}

TEST(FunctionDeclParsing, DpiImportFunctionIntResultAccepted) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int read_word();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

TEST(FunctionDeclParsing, DpiImportFunctionLongintResultAccepted) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function longint read_double();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kLongint);
}

TEST(FunctionDeclParsing, DpiImportFunctionShortrealResultAccepted) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function shortreal measure();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kShortreal);
}

}  // namespace
