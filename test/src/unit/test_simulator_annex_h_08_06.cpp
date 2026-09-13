#include <gtest/gtest.h>

#include <cstdint>
#include <type_traits>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

// Annex H.8.6 (Argument passing by handle, open arrays): an argument
// specified as an open, unsized array is always passed by a handle,
// regardless of the direction of the SystemVerilog formal, and is reached
// through library functions; the implementation of a handle is tool
// specific and transparent to the user, the handle being the generic
// pointer void* under the name svOpenArrayHandle; and an argument passed by
// handle shall always have a const qualifier, because the user shall not
// modify the contents of a handle. The cases check the mode and C type an
// open array takes under every direction and type, the handle's own type,
// and that the array behind it is reached through the library functions.

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

// §H.8.6: by handle whatever the direction, and whatever the element type,
// the C type being const svOpenArrayHandle every time.
TEST(DpiPassingByHandle, AnOpenArrayIsAHandleUnderEveryDirectionAndType) {
  for (const Direction kDirection :
       {Direction::kInput, Direction::kOutput, Direction::kInout}) {
    for (const DataTypeKind kType :
         {DataTypeKind::kInt, DataTypeKind::kBit, DataTypeKind::kStruct}) {
      const DpiArg kFormal = Formal(kType, kDirection, 8);
      EXPECT_EQ(DpiPassingModeOfFormal(kFormal, true),
                DpiPassingMode::kByHandle);
      EXPECT_EQ(DpiCTypeOfFormal(kFormal, true), DpiCTypeOfHandleArgument());
    }
  }
  EXPECT_EQ(DpiCTypeOfHandleArgument(), "const svOpenArrayHandle");
  EXPECT_FALSE(DpiUserMayModifyHandleContents());
}

// §H.8.6: the handle is the generic pointer, and what it points to is the
// tool's own -- the user reaches the array's dimensions and bounds through
// the library functions of §H.12.2 and never through the pointer's type.
TEST(DpiPassingByHandle, TheHandleIsAGenericPointerReadThroughTheLibrary) {
  EXPECT_TRUE((std::is_same<svOpenArrayHandle, void*>::value));
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {3, 1}, {2, 5}};
  SvOpenArrayDesc desc;
  desc.data = nullptr;
  desc.n_dims = 3;
  desc.ranges = kRanges;
  desc.elem_size = 0;
  const svOpenArrayHandle kHandle = &desc;
  EXPECT_TRUE(std::is_const<decltype(kHandle)>::value);
  EXPECT_EQ(svDimensions(kHandle), 3);
  EXPECT_EQ(svLow(kHandle, 1), 1);
  EXPECT_EQ(svHigh(kHandle, 1), 3);
  EXPECT_EQ(svLeft(kHandle, 2), 2);
  EXPECT_EQ(svRight(kHandle, 2), 5);
}

}  // namespace
