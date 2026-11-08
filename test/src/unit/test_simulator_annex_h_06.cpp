#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

TEST(DpiSemanticConstraints, TheCallerCoercesAPackedActualToTheFormalsWidth) {
  EXPECT_EQ(DpiCoercionOfPackedActual(40, 32), DpiActualCoercion::kTruncate);
  EXPECT_EQ(DpiCoercionOfPackedActual(8, 16), DpiActualCoercion::kExtend);
  EXPECT_EQ(DpiCoercionOfPackedActual(16, 16), DpiActualCoercion::kNone);
  EXPECT_EQ(DpiCoercionOfPackedActual(33, 32), DpiActualCoercion::kTruncate);
  EXPECT_EQ(DpiCoercionOfPackedActual(32, 33), DpiActualCoercion::kExtend);
}

TEST(DpiSemanticConstraints, TheCTypeShallMatchTheFormalsType) {
  const DpiArg kIntIn = Formal(DataTypeKind::kInt, Direction::kInput);
  EXPECT_TRUE(DpiCTypeMatchesFormal(kIntIn, false, "const int"));
  EXPECT_FALSE(DpiCTypeMatchesFormal(kIntIn, false, "unsigned int"));
  const DpiArg kIntOut = Formal(DataTypeKind::kInt, Direction::kOutput);
  EXPECT_TRUE(DpiCTypeMatchesFormal(kIntOut, false, "int*"));
  EXPECT_TRUE(DpiCTypeMatchesFormal(kIntOut, false, "int *"));
  EXPECT_FALSE(DpiCTypeMatchesFormal(kIntOut, false, "const int"));
  const DpiArg kBitsIn = Formal(DataTypeKind::kBit, Direction::kInput, 8);
  EXPECT_TRUE(DpiCTypeMatchesFormal(kBitsIn, false, "const svBitVecVal *"));
  EXPECT_FALSE(DpiCTypeMatchesFormal(kBitsIn, false, "const unsigned char"));
  const DpiArg kBitsOut = Formal(DataTypeKind::kBit, Direction::kOutput, 8);
  EXPECT_TRUE(DpiCTypeMatchesFormal(kBitsOut, false, "svBitVecVal*"));
  EXPECT_FALSE(DpiCTypeMatchesFormal(kBitsOut, false, "svLogicVecVal*"));
  EXPECT_TRUE(DpiCTypeMatchesFormal(kBitsOut, true, "const svOpenArrayHandle"));
  EXPECT_FALSE(DpiCTypeMatchesFormal(kBitsOut, true, "svBitVecVal*"));
}

}  // namespace
