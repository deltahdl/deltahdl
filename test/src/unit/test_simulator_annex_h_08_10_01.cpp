#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

namespace {

DpiArg StringFormal(Direction direction) {
  DpiArg formal;
  formal.name = "s";
  formal.type = DataTypeKind::kString;
  formal.direction = direction;
  return formal;
}

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

TEST(DpiStringMembers, AStringMemberFollowsTheStandaloneStipulations) {
  EXPECT_TRUE(DpiStringMemberStipulationsAreStandalone());
  EXPECT_EQ(
      DpiSideProvidingStringPointer(DpiStringPointerProvider::kImportInput),
      DpiMemorySide::kSystemVerilog);
  EXPECT_EQ(DpiSideCopyingString(DpiStringPointerProvider::kImportInoutChanged),
            DpiMemorySide::kSystemVerilog);
  EXPECT_FALSE(DpiStringCharactersMayBeModifiedByReceiver());
}

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
