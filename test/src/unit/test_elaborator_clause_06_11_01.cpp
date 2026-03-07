// §6.11.1

#include "elaborator/type_eval.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §6.11.1: All basic integer data types are integral.
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

}  // namespace
