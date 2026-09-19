#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

// Annex H.8.5 (Allocating actual arguments for SystemVerilog-specific
// types): relevant only to calling an exported SystemVerilog subroutine
// from C, where the caller is responsible for allocating every actual
// passed by reference; static allocation requires knowledge of the data
// type, and where the type involves SystemVerilog packed arrays a C array
// of the canonical type, svLogicVecVal or svBitVecVal, is allocated and
// initialized before being passed by reference to the export. The cases
// check which actuals the caller allocates and the C declaration that
// allocates each.

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

// §H.8.5: the caller allocates an actual passed by reference -- an output
// or inout of any type, an input packed array -- and not one passed by
// value, which it hands over as it is.
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

// §H.8.5: a small type's actual is one C object of Table H.1's type, and a
// packed array's is a C array of the canonical type with one element per
// 32 bits -- svBitVecVal v[1] for bit [7:0], svLogicVecVal w[2] for logic
// [39:0], svLogicVecVal t[2] for a time -- whatever the direction, the
// const of an input being the export's to see and not the allocation's.
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
