#include <gtest/gtest.h>

#include <vector>

#include "elaborator/cross_automatic_types.h"

using namespace delta;

namespace {

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

TEST(CrossAutomaticTypes, CrossValTypeWithNoCoverpointsHasNoMembers) {
  CrossValTypeDef def = BuildCrossValType({});
  EXPECT_TRUE(def.members.empty());
}

TEST(CrossAutomaticTypes, DefaultBoundsUseBitsMinusOne) {
  EXPECT_EQ(CrossValMemberDefaultBoundType(12), "logic [11:0]");
  EXPECT_EQ(CrossValMemberDefaultBoundType(1), "logic [0:0]");
  EXPECT_EQ(CrossValMemberDefaultBoundType(0), "logic [0:0]");
}

TEST(CrossAutomaticTypes, CrossQueueTypeIsUnboundedQueueOfCrossValType) {
  CrossQueueTypeDef def = BuildCrossQueueType();
  EXPECT_EQ(def.element_type, kCrossValTypeName);
  EXPECT_TRUE(def.unbounded);
}

TEST(CrossAutomaticTypes, AutoTypesVisibleOnlyInsideDefiningCross) {
  EXPECT_TRUE(CrossAutoTypeIsVisible("XYA", "XYA"));
  EXPECT_FALSE(CrossAutoTypeIsVisible("OtherCross", "XYA"));
  EXPECT_FALSE(CrossAutoTypeIsVisible("covergroup_scope", "XYA"));
}

TEST(CrossAutomaticTypes, CrossTypeNamesAreImplicitTypedefs) {
  EXPECT_TRUE(IsImplicitCrossTypedefName("CrossValType"));
  EXPECT_TRUE(IsImplicitCrossTypedefName("CrossQueueType"));
  EXPECT_EQ(kCrossValTypeName, "CrossValType");
  EXPECT_EQ(kCrossQueueTypeName, "CrossQueueType");
  EXPECT_FALSE(IsImplicitCrossTypedefName("SomeOtherType"));
}

}  // namespace
