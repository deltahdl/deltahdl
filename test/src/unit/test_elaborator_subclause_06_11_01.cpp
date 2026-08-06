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

TEST(SimpleBitVectorType, NonIntegerKindsAreNotSimpleBitVectorTypes) {
  EXPECT_FALSE(IsSimpleBitVectorType(DataTypeKind::kReal));
  EXPECT_FALSE(IsSimpleBitVectorType(DataTypeKind::kShortreal));
  EXPECT_FALSE(IsSimpleBitVectorType(DataTypeKind::kString));
  EXPECT_FALSE(IsSimpleBitVectorType(DataTypeKind::kVoid));
  EXPECT_FALSE(IsSimpleBitVectorType(DataTypeKind::kEnum));
  EXPECT_FALSE(IsSimpleBitVectorType(DataTypeKind::kChandle));
}

TEST(SimpleBitVectorType, PackedStructIsNotSimpleBitVectorType) {
  DataType packed_struct;
  packed_struct.kind = DataTypeKind::kStruct;
  packed_struct.is_packed = true;
  EXPECT_FALSE(IsSimpleBitVectorType(packed_struct));
}

TEST(SimpleBitVectorType, PackedUnionIsNotSimpleBitVectorType) {
  DataType packed_union;
  packed_union.kind = DataTypeKind::kUnion;
  packed_union.is_packed = true;
  EXPECT_FALSE(IsSimpleBitVectorType(packed_union));
}

TEST(SimpleBitVectorType, MultidimensionalPackedArrayIsNotSimpleBitVectorType) {
  DataType multidim;
  multidim.kind = DataTypeKind::kLogic;
  multidim.extra_packed_dims.push_back({nullptr, nullptr});
  EXPECT_FALSE(IsSimpleBitVectorType(multidim));
}

TEST(SimpleBitVectorType, OneDimensionalPackedLogicIsSimpleBitVectorType) {
  DataType v;
  v.kind = DataTypeKind::kLogic;

  EXPECT_TRUE(IsSimpleBitVectorType(v));
}

}  // namespace
