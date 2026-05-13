

#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ScalarAndVectorDeclaration, ScalarNoRange) {
  auto r = Parse(
      "module t;\n"
      "  logic a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, RegScalarNoRange) {
  auto r = Parse(
      "module t;\n"
      "  reg a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_EQ(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, BitScalarNoRange) {
  auto r = Parse(
      "module t;\n"
      "  bit a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_EQ(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, RangeProducesDimensions) {
  auto r = Parse(
      "module t;\n"
      "  logic [3:0] a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_NE(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, RegRangeProducesDimensions) {
  auto r = Parse(
      "module t;\n"
      "  reg [3:0] r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_NE(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, BitRangeProducesDimensions) {
  auto r = Parse(
      "module t;\n"
      "  bit [3:0] b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_NE(item->data_type.packed_dim_right, nullptr);
}

// §6.9: An object declared implicitly as logic without a range is a scalar.
// The parser shall leave the packed-dimension fields null for `var v;`.
TEST(ScalarAndVectorDeclaration, ImplicitLogicScalarHasNoPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  var v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right, nullptr);
}

// §6.9: The multibit-vector rule applies to implicit logic; a `var [7:0] v;`
// declaration shall carry a packed range and parse as a vector.
TEST(ScalarAndVectorDeclaration, ImplicitLogicVectorHasPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  var [7:0] v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_NE(item->data_type.packed_dim_right, nullptr);
}

// §6.9: "Vectors are packed arrays of scalars (see 7.4)." A `logic [7:0] v;`
// is the §6.9 vector and shall be recognised as such by the shared
// IsVector predicate.
TEST(ScalarAndVectorDeclaration, VectorIsRecognisedByIsVector) {
  auto r = Parse("module t; logic [7:0] v; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(IsVector(item->data_type));
}

// §6.9: A scalar reg/logic/bit (no range) is not a vector. The shared
// IsVector predicate distinguishes scalar from vector at the parser stage.
TEST(ScalarAndVectorDeclaration, ScalarIsNotRecognisedByIsVector) {
  auto r = Parse("module t; logic v; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_FALSE(IsVector(item->data_type));
}

// §6.9: The "vector = packed-array-of-scalars" equivalence applies to reg
// just as to logic — a `reg [3:0] r;` is a §6.9 vector.
TEST(ScalarAndVectorDeclaration, RegVectorIsRecognisedByIsVector) {
  auto r = Parse("module t; reg [3:0] r; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(IsVector(item->data_type));
}

// §6.9: The "vector = packed-array-of-scalars" equivalence applies to bit
// — a `bit [3:0] b;` is a §6.9 vector.
TEST(ScalarAndVectorDeclaration, BitVectorIsRecognisedByIsVector) {
  auto r = Parse("module t; bit [3:0] b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(IsVector(item->data_type));
}

// §6.9: A `var [N:M] v;` is a multibit object whose implicit element type
// is logic. The equivalence applies, so IsVector recognises it as a vector.
TEST(ScalarAndVectorDeclaration, ImplicitLogicVectorIsRecognisedByIsVector) {
  auto r = Parse("module t; var [7:0] v; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(IsVector(item->data_type));
}

// §6.9: A "matching user-defined type" of a packed reg/logic/bit is itself
// a §6.9 vector. The typedef-aware IsVector overload resolves the named
// type through a typedef map and recognises the resulting vector.
TEST(ScalarAndVectorDeclaration, MatchingUserDefinedTypeVectorIsVector) {
  auto r = Parse(
      "module t;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  byte_t v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  TypedefMap typedefs;
  const ModuleItem* var = nullptr;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kTypedef) {
      typedefs.emplace(it->name, it->data_type);
    } else if (it->kind == ModuleItemKind::kVarDecl) {
      var = it;
    }
  }
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->data_type.kind, DataTypeKind::kNamed);
  EXPECT_FALSE(IsVector(var->data_type));
  EXPECT_TRUE(IsVector(var->data_type, typedefs));
}

// §6.9: A typedef of a scalar reg/logic/bit is NOT a vector — even when
// resolved through the typedef map, it has no packed dimension and so
// fails the §6.9 vector definition.
TEST(ScalarAndVectorDeclaration, MatchingUserDefinedTypeScalarIsNotVector) {
  auto r = Parse(
      "module t;\n"
      "  typedef logic my_logic_t;\n"
      "  my_logic_t v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  TypedefMap typedefs;
  const ModuleItem* var = nullptr;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kTypedef) {
      typedefs.emplace(it->name, it->data_type);
    } else if (it->kind == ModuleItemKind::kVarDecl) {
      var = it;
    }
  }
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(IsVector(var->data_type, typedefs));
}

// §6.9: The "vector" of §6.9 is multibit "by specifying a range" — a single
// range. A packed object with more than one range (a multidimensional
// packed array) is outside §6.9's vector definition. IsVector returns
// false even though packed dimensions are present.
TEST(ScalarAndVectorDeclaration, MultidimensionalPackedArrayIsNotAVector) {
  auto r = Parse("module t; logic [3:0][7:0] m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_FALSE(item->data_type.extra_packed_dims.empty());
  EXPECT_FALSE(IsVector(item->data_type));
}

}  // namespace
