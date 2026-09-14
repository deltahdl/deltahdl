#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

namespace {

// A formal named s of the type and direction, an unpacked array of them
// once dimensions are given.
DpiArg StringFormal(Direction direction) {
  DpiArg formal;
  formal.name = "s";
  formal.type = DataTypeKind::kString;
  formal.direction = direction;
  return formal;
}

// §H.8.10.1: a string contained in an aggregate argument is represented by
// a const char* member, the type Table H.1 gives a stand-alone string, and
// an aggregate carrying one is an argument the interface takes.
TEST(DpiStringMembers, AStringMemberOfAnAggregateIsAConstCharPointer) {
  EXPECT_EQ(DpiCTypeOfStringMember(), "const char*");
  EXPECT_EQ(DpiCTypeOfStringMember(),
            DpiCTypeOfBasicType(DataTypeKind::kString, false));
  DpiAggregateElement record;
  record.kind = DataTypeKind::kStruct;
  record.members = {DpiAggregateElement{DataTypeKind::kString, 0, {}},
                    DpiAggregateElement{DataTypeKind::kInt, 0, {}}};
  EXPECT_TRUE(DpiAggregateIsAnArgument(record));
}

// §H.8.10.1: all the same stipulations apply to a string member as to a
// stand-alone string -- the side that provided the pointer owns the
// storage and copies nothing, the receiving side copies what it keeps and
// never modifies the characters.
TEST(DpiStringMembers, AStringMemberFollowsTheStandaloneStipulations) {
  EXPECT_TRUE(DpiStringMemberStipulationsAreStandalone());
  EXPECT_EQ(
      DpiSideProvidingStringPointer(DpiStringPointerProvider::kImportInput),
      DpiMemorySide::kSystemVerilog);
  EXPECT_EQ(DpiSideCopyingString(DpiStringPointerProvider::kImportInoutChanged),
            DpiMemorySide::kSystemVerilog);
  EXPECT_FALSE(DpiStringCharactersMayBeModifiedByReceiver());
}

// §H.8.10.1 NOTE with §H.7.8: an array of strings is const char** in every
// direction, the array's own indirection over its const char* elements
// and not the extra level a stand-alone output or inout string takes, so an
// input array is not a stand-alone input's const char* and an output array
// is not a const char*** over a stand-alone output's const char**.
TEST(DpiStringMembers, AnArrayOfStringsIsConstCharPointerPointerRegardless) {
  for (const Direction kDirection :
       {Direction::kInput, Direction::kOutput, Direction::kInout}) {
    EXPECT_EQ(DpiCTypeOfStringArray(kDirection), "const char**");
  }
  EXPECT_NE(DpiCTypeOfStringArray(Direction::kInput),
            DpiCTypeOfFormal(StringFormal(Direction::kInput), false));
  EXPECT_EQ(DpiCTypeOfStringArray(Direction::kOutput),
            DpiCTypeOfFormal(StringFormal(Direction::kOutput), false));
  EXPECT_EQ(DpiCTypeOfStringArray(Direction::kInout),
            DpiCTypeOfFormal(StringFormal(Direction::kInout), false));
}

// §H.8.10.1 NOTE with §H.11.4: an unpacked array of strings `string s [3]`
// is declared to C as `const char* s[3]` whatever its direction, the const
// the element's own and not one more the input direction adds, whereas an
// input array of int still takes the direction's const.
TEST(DpiStringMembers, AnUnpackedArrayOfStringsIsDeclaredTheSameInEveryMode) {
  const std::vector<SvActualDimension> kThree = {{0, 2}};
  for (const Direction kDirection :
       {Direction::kInput, Direction::kOutput, Direction::kInout}) {
    EXPECT_EQ(DpiCDeclarationOfUnpackedFormal(StringFormal(kDirection), kThree),
              "const char* s[3]");
  }
  DpiArg ints = StringFormal(Direction::kInput);
  ints.type = DataTypeKind::kInt;
  EXPECT_EQ(DpiCDeclarationOfUnpackedFormal(ints, kThree), "const int s[3]");
}

}  // namespace
