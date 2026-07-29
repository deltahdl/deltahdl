#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(IntegralIndexAssocArrayParsing, AssocDimByteType) {
  auto r = Parse("module m; int aa [byte]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->text, "byte");
}
TEST(IntegralIndexAssocArrayParsing, AssocArrayIntIndex) {
  auto r = Parse(
      "module t;\n"
      "  byte lookup[int];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "lookup");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(item->unpacked_dims[0]->text, "int");
}

TEST(IntegralIndexAssocArrayParsing, AssocArrayIntegerIndex) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] cache[integer];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "cache");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "integer");
}

// §7.8 makes an index_type a data_type, and A.2.2.1 gives
// `integer_atom_type [ signing ]`, so an integral index type accepts an
// explicit unsigned. The qualifier is recorded on the dimension because it
// decides how the keys order.
TEST(IntegralIndexAssocArrayParsing, AssocDimByteUnsignedType) {
  auto r = Parse("module m; int aa [byte unsigned]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->text, "byte");
  EXPECT_EQ(item->unpacked_dims[0]->op, TokenKind::kKwUnsigned);
}

// The same production admits `signed`, which every integer atom type already
// is by default. Naming it explicitly parses and is recorded.
TEST(IntegralIndexAssocArrayParsing, AssocDimIntSignedType) {
  auto r = Parse("module m; int aa [int signed]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->op, TokenKind::kKwSigned);
}

// A.2.2.1 attaches signing to the integer types alone. `string` is a data_type
// in its own right with no signing in its production, so a qualifier after it
// is not an index type this grammar admits.
TEST(IntegralIndexAssocArrayParsing, AssocDimStringTakesNoSigning) {
  auto r = Parse("module m; int aa [string unsigned]; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// An integral index type with no qualifier records none, so the default
// signedness of the type itself stands.
TEST(IntegralIndexAssocArrayParsing, AssocDimByteRecordsNoSigningByDefault) {
  auto r = Parse("module m; int aa [byte]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->op, TokenKind::kEof);
}

}  // namespace
