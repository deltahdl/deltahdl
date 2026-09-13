#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

// Annex H.8.4 (Argument passing by reference): an argument passed by
// reference is passed as a pointer to the actual data object, and for
// packed data as a pointer to a canonical data object; an argument of type
// T passed by reference has a formal of type T*, a packed array a pointer
// to the canonical type, svLogicVecVal* or svBitVecVal*; and a DPI C
// application shall make no assumption about the lifetime of an argument
// passed by reference, so a value to keep across calls is copied into
// memory the C application owns and manages. The cases check what the
// pointer refers to and its type for each kind of formal, and that the
// reference is not to be kept.

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

// §H.8.4: a T passed by reference is a T* -- int*, double*, void** for a
// chandle, const char** for a string -- and packed data a pointer to its
// canonical object, svBitVecVal* or svLogicVecVal*, const for an input.
TEST(DpiPassingByReference, AReferenceIsAPointerToTheTypeOrItsCanonicalForm) {
  EXPECT_EQ(DpiReferentOfFormal(Formal(DataTypeKind::kInt, Direction::kOutput)),
            DpiReferent::kActualDataObject);
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kInt, Direction::kOutput), false),
      "int*");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kReal, Direction::kInout), false),
      "double*");
  EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kChandle, Direction::kInout),
                             false),
            "void**");
  EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kString, Direction::kOutput),
                             false),
            "const char**");
  EXPECT_EQ(
      DpiReferentOfFormal(Formal(DataTypeKind::kBit, Direction::kOutput, 8)),
      DpiReferent::kCanonicalDataObject);
  EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kBit, Direction::kOutput, 8),
                             false),
            "svBitVecVal*");
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kLogic, Direction::kInout, 40), false),
            "svLogicVecVal*");
  EXPECT_EQ(
      DpiReferentOfFormal(Formal(DataTypeKind::kLogic, Direction::kInput, 40)),
      DpiReferent::kCanonicalDataObject);
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kLogic, Direction::kInput, 40), false),
            "const svLogicVecVal*");
  EXPECT_EQ(
      DpiReferentOfFormal(Formal(DataTypeKind::kInteger, Direction::kInput)),
      DpiReferent::kCanonicalDataObject);
}

// §H.8.4: no assumption holds about the lifetime of a reference beyond the
// call, and a value kept across calls lives in memory the C application
// owns.
TEST(DpiPassingByReference, AReferenceIsNotToBeKeptAcrossCalls) {
  EXPECT_FALSE(DpiReferenceOutlivesTheCall());
  EXPECT_EQ(DpiSideOwningACopyKeptAcrossCalls(), DpiMemorySide::kC);
}

}  // namespace
