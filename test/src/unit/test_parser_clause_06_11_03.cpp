// §6.11.3: Signed and unsigned integer types

#include "fixture_parser.h"

using namespace delta;

namespace {

// integer_atom_type [signing]
TEST(ParserA221, DataTypeIntegerAtom) {
  auto r = Parse("module m; int unsigned x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(item->data_type.is_signed);
}

TEST(ParserA221, SigningUnsigned) {
  auto r = Parse("module m; integer unsigned x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->items[0]->data_type.is_signed);
}

// --- data_type --- (12 alternatives)
// integer_vector_type [signing] {packed_dimension}
TEST(ParserA221, DataTypeIntegerVector) {
  auto r = Parse("module m; logic signed [7:0] a; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
}

}  // namespace
