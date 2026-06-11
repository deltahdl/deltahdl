#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"
#include "fixture_program.h"

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

// §35.5.5: "An imported function declaration shall explicitly specify a data
// type or void for the type of the function's return result." An omitted
// (implicit) return type -- legal for a native function -- is rejected here.
TEST(FunctionDeclParsing, DpiImportFunctionImplicitReturnTypeRejected) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function get_value(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

// §35.5.5: chandle is one of the data types allowed for imported function
// results, so a chandle-returning import parses without error.
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

// §35.5.5: "Scalar values of type bit and logic" are permitted results. A bare
// (single-bit, unpacked) bit return type is accepted.
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

// §35.5.5: "Scalar values of type bit and logic" are permitted results. The
// logic half of that pair is accepted in its scalar (single-bit) form, just as
// scalar bit is.
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

// §35.5.5: real is one of the data types allowed for imported function
// results, covering the floating-point category of the permitted small-value
// list.
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

// §35.5.5: only the *scalar* form of logic is a permitted result. A packed
// logic vector is rejected, mirroring the packed-bit case for the logic half of
// the permitted bit/logic pair.
TEST(FunctionDeclParsing, DpiImportFunctionPackedLogicResultRejected) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function logic [3:0] read_nibble();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

// §35.5.5: the permitted result list excludes the wide 4-state 'time' type, so
// a time-returning import is rejected -- a distinct exclusion from the integer
// case.
TEST(FunctionDeclParsing, DpiImportFunctionTimeResultRejected) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function time stamp();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

// §35.5.5: results are restricted to *small values*. A packed bit vector is not
// a scalar bit value and is therefore not a permitted result type.
TEST(FunctionDeclParsing, DpiImportFunctionPackedBitResultRejected) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function bit [7:0] read_byte();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

// §35.5.5: the allowed result list excludes the wide 4-state 'integer' type
// (permitted only as a formal argument under §35.5.6), so an integer-returning
// import is rejected.
TEST(FunctionDeclParsing, DpiImportFunctionIntegerResultRejected) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function integer count();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

}
