#include <gtest/gtest.h>

#include "elaborator/cross_automatic_types.h"

using namespace delta;

namespace {

// §19.6.1.3: CrossValType is a SystemVerilog struct consisting of one member for
// each coverpoint in the cross; the name and type of each field are the name and
// type of the corresponding coverpoint, in order.
TEST(CrossAutomaticTypes, CrossValTypeHasOneMemberPerCoverpoint) {
  std::vector<CrossValMember> coverpoints = {
      {"xy", "logic [11:0]"},
      {"a", "logic [0:2]"},
  };
  CrossValTypeDef def = BuildCrossValType(coverpoints);

  ASSERT_EQ(def.members.size(), 2u);
  EXPECT_EQ(def.members[0].name, "xy");
  EXPECT_EQ(def.members[0].type, "logic [11:0]");
  EXPECT_EQ(def.members[1].name, "a");
  EXPECT_EQ(def.members[1].type, "logic [0:2]");
}

// §19.6.1.3 edge case: a CrossValType built from no coverpoints yields a struct
// with no members — BuildCrossValType maps one member per coverpoint, so an
// empty coverpoint list maps to an empty member list.
TEST(CrossAutomaticTypes, CrossValTypeWithNoCoverpointsHasNoMembers) {
  CrossValTypeDef def = BuildCrossValType({});
  EXPECT_TRUE(def.members.empty());
}

// §19.6.1.3: when range bounds for the coverpoint type are not evident, the
// bounds are assumed to be [$bits(coverpoint_expression)-1:0].
TEST(CrossAutomaticTypes, DefaultBoundsUseBitsMinusOne) {
  EXPECT_EQ(CrossValMemberDefaultBoundType(12), "logic [11:0]");
  EXPECT_EQ(CrossValMemberDefaultBoundType(1), "logic [0:0]");
  // A coverpoint expression always occupies at least one bit.
  EXPECT_EQ(CrossValMemberDefaultBoundType(0), "logic [0:0]");
}

// §19.6.1.3: CrossQueueType is an unbounded queue of CrossValType elements.
TEST(CrossAutomaticTypes, CrossQueueTypeIsUnboundedQueueOfCrossValType) {
  CrossQueueTypeDef def = BuildCrossQueueType();
  EXPECT_EQ(def.element_type, kCrossValTypeName);
  EXPECT_TRUE(def.unbounded);
}

// §19.6.1.3: the scope of the type names is the cross itself; the types are not
// accessible outside this scope.
TEST(CrossAutomaticTypes, AutoTypesVisibleOnlyInsideDefiningCross) {
  EXPECT_TRUE(CrossAutoTypeIsVisible("XYA", "XYA"));
  EXPECT_FALSE(CrossAutoTypeIsVisible("OtherCross", "XYA"));
  EXPECT_FALSE(CrossAutoTypeIsVisible("covergroup_scope", "XYA"));
}

// §19.6.1.3: the cross types shall be considered as implicit typedefs in the
// body of the cross.
TEST(CrossAutomaticTypes, CrossTypeNamesAreImplicitTypedefs) {
  EXPECT_TRUE(IsImplicitCrossTypedefName("CrossValType"));
  EXPECT_TRUE(IsImplicitCrossTypedefName("CrossQueueType"));
  EXPECT_EQ(kCrossValTypeName, "CrossValType");
  EXPECT_EQ(kCrossQueueTypeName, "CrossQueueType");
  EXPECT_FALSE(IsImplicitCrossTypedefName("SomeOtherType"));
}

}  // namespace
