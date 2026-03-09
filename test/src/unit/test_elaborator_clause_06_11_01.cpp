

#include "elaborator/type_eval.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TypeEval, IntegerTypesAreIntegral) {
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

TEST(TypeEval, EnumIsIntegral) {
  EXPECT_TRUE(IsIntegralType(DataTypeKind::kEnum));
}

TEST(TypeEval, NonIntegralTypes) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kReal));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kShortreal));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kRealtime));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kString));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kVoid));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kChandle));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kEvent));
}

TEST(TypeEval, IntegerTypeWidths) {
  DataType dt;
  dt.kind = DataTypeKind::kByte;
  EXPECT_EQ(EvalTypeWidth(dt), 8u);
  dt.kind = DataTypeKind::kShortint;
  EXPECT_EQ(EvalTypeWidth(dt), 16u);
  dt.kind = DataTypeKind::kInt;
  EXPECT_EQ(EvalTypeWidth(dt), 32u);
  dt.kind = DataTypeKind::kLongint;
  EXPECT_EQ(EvalTypeWidth(dt), 64u);
  dt.kind = DataTypeKind::kInteger;
  EXPECT_EQ(EvalTypeWidth(dt), 32u);
  dt.kind = DataTypeKind::kTime;
  EXPECT_EQ(EvalTypeWidth(dt), 64u);
}

}
