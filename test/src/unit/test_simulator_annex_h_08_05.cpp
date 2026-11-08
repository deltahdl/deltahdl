#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

namespace {

DpiArg Formal(const char* name, DataTypeKind type, Direction direction,
              uint32_t width = 0) {
  DpiArg formal;
  formal.name = name;
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

TEST(DpiExportActualAllocation, TheCallerAllocatesWhatIsPassedByReference) {
  EXPECT_TRUE(DpiCallerAllocatesExportActual(
      Formal("o", DataTypeKind::kInt, Direction::kOutput)));
  EXPECT_TRUE(DpiCallerAllocatesExportActual(
      Formal("io", DataTypeKind::kReal, Direction::kInout)));
  EXPECT_TRUE(DpiCallerAllocatesExportActual(
      Formal("v", DataTypeKind::kBit, Direction::kInput, 8)));
  EXPECT_FALSE(DpiCallerAllocatesExportActual(
      Formal("i", DataTypeKind::kInt, Direction::kInput)));
  EXPECT_FALSE(DpiCallerAllocatesExportActual(
      Formal("s", DataTypeKind::kString, Direction::kInput)));
}

TEST(DpiExportActualAllocation, APackedActualIsACArrayOfCanonicalChunks) {
  EXPECT_EQ(DpiCAllocationOfExportActual(
                Formal("o", DataTypeKind::kInt, Direction::kOutput)),
            "int o");
  EXPECT_EQ(DpiCAllocationOfExportActual(
                Formal("io", DataTypeKind::kReal, Direction::kInout)),
            "double io");
  EXPECT_EQ(DpiCAllocationOfExportActual(
                Formal("v", DataTypeKind::kBit, Direction::kInput, 8)),
            "svBitVecVal v[1]");
  EXPECT_EQ(DpiCAllocationOfExportActual(
                Formal("w", DataTypeKind::kLogic, Direction::kOutput, 40)),
            "svLogicVecVal w[2]");
  EXPECT_EQ(DpiCAllocationOfExportActual(
                Formal("t", DataTypeKind::kTime, Direction::kInout)),
            "svLogicVecVal t[2]");
  EXPECT_EQ(DpiCAllocationOfExportActual(
                Formal("e", DataTypeKind::kEvent, Direction::kInput)),
            "");
}

}  // namespace
