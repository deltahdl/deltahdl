#include <gtest/gtest.h>

#include "elaborator/type_eval.h"
#include "parser/ast.h"

using namespace delta;

namespace {

TEST(IntegralType, IntegerTypesAreIntegral) {
  EXPECT_TRUE(IsIntegralType(DataTypeKind::kBit));
  EXPECT_TRUE(IsIntegralType(DataTypeKind::kLogic));
  EXPECT_TRUE(IsIntegralType(DataTypeKind::kReg));
  EXPECT_TRUE(IsIntegralType(DataTypeKind::kByte));
  EXPECT_TRUE(IsIntegralType(DataTypeKind::kShortint));
  EXPECT_TRUE(IsIntegralType(DataTypeKind::kInt));
  EXPECT_TRUE(IsIntegralType(DataTypeKind::kLongint));
  EXPECT_TRUE(IsIntegralType(DataTypeKind::kInteger));
  EXPECT_TRUE(IsIntegralType(DataTypeKind::kTime));
}

TEST(IntegralType, EnumIsIntegral) {
  EXPECT_TRUE(IsIntegralType(DataTypeKind::kEnum));
}

TEST(IntegralType, NonIntegralTypes) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kReal));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kShortreal));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kRealtime));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kString));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kVoid));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kChandle));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kEvent));
}

TEST(IntegralType, ImplicitTypeIsIntegral) {
  EXPECT_TRUE(IsIntegralType(DataTypeKind::kImplicit));
}

// §6.11.1: "The integer types listed in Table 6-8 are simple bit vector
// types with predefined widths." All nine Table 6-8 kinds qualify.
TEST(SimpleBitVectorType, BuiltInIntegerKindsAreSimpleBitVectorTypes) {
  EXPECT_TRUE(IsSimpleBitVectorType(DataTypeKind::kBit));
  EXPECT_TRUE(IsSimpleBitVectorType(DataTypeKind::kLogic));
  EXPECT_TRUE(IsSimpleBitVectorType(DataTypeKind::kReg));
  EXPECT_TRUE(IsSimpleBitVectorType(DataTypeKind::kByte));
  EXPECT_TRUE(IsSimpleBitVectorType(DataTypeKind::kShortint));
  EXPECT_TRUE(IsSimpleBitVectorType(DataTypeKind::kInt));
  EXPECT_TRUE(IsSimpleBitVectorType(DataTypeKind::kLongint));
  EXPECT_TRUE(IsSimpleBitVectorType(DataTypeKind::kInteger));
  EXPECT_TRUE(IsSimpleBitVectorType(DataTypeKind::kTime));
}

// §6.11.1: Non-integer kinds do not directly represent a packed array of
// bits — they are not simple bit vector types.
TEST(SimpleBitVectorType, NonIntegerKindsAreNotSimpleBitVectorTypes) {
  EXPECT_FALSE(IsSimpleBitVectorType(DataTypeKind::kReal));
  EXPECT_FALSE(IsSimpleBitVectorType(DataTypeKind::kShortreal));
  EXPECT_FALSE(IsSimpleBitVectorType(DataTypeKind::kString));
  EXPECT_FALSE(IsSimpleBitVectorType(DataTypeKind::kVoid));
  EXPECT_FALSE(IsSimpleBitVectorType(DataTypeKind::kEnum));
  EXPECT_FALSE(IsSimpleBitVectorType(DataTypeKind::kChandle));
}

// §6.11.1: "The packed structure (see 7.2.1) ... and multidimensional packed
// array types (see 7.4) are not simple bit vector types, but each is
// equivalent (see 6.22.2) to some simple bit vector type." A packed struct's
// underlying kind is kStruct with is_packed=true.
TEST(SimpleBitVectorType, PackedStructIsNotSimpleBitVectorType) {
  DataType packed_struct;
  packed_struct.kind = DataTypeKind::kStruct;
  packed_struct.is_packed = true;
  EXPECT_FALSE(IsSimpleBitVectorType(packed_struct));
}

// §6.11.1 + §7.2.2: A packed union is likewise equivalent to but not a
// simple bit vector type. (§7.2.2 is the cross-referenced subclause that
// defines the kUnion shape with is_packed=true.)
TEST(SimpleBitVectorType, PackedUnionIsNotSimpleBitVectorType) {
  DataType packed_union;
  packed_union.kind = DataTypeKind::kUnion;
  packed_union.is_packed = true;
  EXPECT_FALSE(IsSimpleBitVectorType(packed_union));
}

// §6.11.1: A multidimensional packed array (§7.4) is not a simple bit vector
// type. The DataType uses extra_packed_dims for dimensions past the first.
TEST(SimpleBitVectorType, MultidimensionalPackedArrayIsNotSimpleBitVectorType) {
  DataType multidim;
  multidim.kind = DataTypeKind::kLogic;
  multidim.extra_packed_dims.push_back({nullptr, nullptr});
  EXPECT_FALSE(IsSimpleBitVectorType(multidim));
}

// §6.11.1: A one-dimensional packed bit/logic/reg vector remains a simple
// bit vector type even when an explicit packed range is supplied.
TEST(SimpleBitVectorType, OneDimensionalPackedLogicIsSimpleBitVectorType) {
  DataType v;
  v.kind = DataTypeKind::kLogic;
  // packed_dim_left/right being non-null with empty extra_packed_dims
  // represents a single packed dimension [N:0].
  EXPECT_TRUE(IsSimpleBitVectorType(v));
}

}  // namespace
