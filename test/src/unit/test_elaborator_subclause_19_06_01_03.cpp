#include <gtest/gtest.h>

#include <vector>

#include "elaborator/cross_automatic_types.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

TEST(CrossAutomaticTypes, ACrossTypeNamedInTheModuleIsUndeclared) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [1:0] a, b;\n"
      "  covergroup cg;\n"
      "    ca: coverpoint a; cb: coverpoint b;\n"
      "    X: cross ca, cb {\n"
      "      function CrossQueueType mk(); endfunction\n"
      "      bins s = mk();\n"
      "    }\n"
      "  endgroup\n"
      "  CrossQueueType q0;\n"
      "  CrossValType v0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of type 'CrossQueueType' does not "
                            "precede this reference to it",
                            10, "6.18"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of type 'CrossValType' does not "
                            "precede this reference to it",
                            11, "6.18"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(CrossAutomaticTypes, DISABLED_ACrossTypeNamedInTheCovergroupIsUndeclared) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [1:0] a, b;\n"
      "  covergroup cg;\n"
      "    ca: coverpoint a { bins s[] = {[0:3]} with "
      "($bits(CrossValType) > 0); }\n"
      "    cb: coverpoint b;\n"
      "    X: cross ca, cb;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of type 'CrossValType' does not "
                            "precede this reference to it",
                            4, "6.18"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
