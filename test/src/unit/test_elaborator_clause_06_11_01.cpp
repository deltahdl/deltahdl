

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

TEST(IntegralType, SimpleBitVectorDefaultWidthIsOne) {
  DataType dt;
  dt.kind = DataTypeKind::kBit;
  EXPECT_EQ(EvalTypeWidth(dt), 1u);
  dt.kind = DataTypeKind::kLogic;
  EXPECT_EQ(EvalTypeWidth(dt), 1u);
  dt.kind = DataTypeKind::kReg;
  EXPECT_EQ(EvalTypeWidth(dt), 1u);
}

}  // namespace
