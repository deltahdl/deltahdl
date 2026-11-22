#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr const char* kOperandOrders =
    "module top; logic clk, a, b, c, d;\n"
    "  u1: assert property (@(posedge clk) ##[1:3] a);\n"
    "  u2: assert property (@(posedge clk) ##[2:2] a);\n"
    "  u3: assert property (@(posedge clk) ##[1:$] a);\n"
    "  u4: assert property (@(posedge clk) ##[*] a);\n"
    "  u5: assert property (@(posedge clk) ##[+] a);\n"
    "  b1: assert property (@(posedge clk) a ##[2:2] b);\n"
    "  b2: assert property (@(posedge clk) a ##[1:$] b);\n"
    "  b3: assert property (@(posedge clk) a ##[*] b);\n"
    "  b4: assert property (@(posedge clk) a ##[+] b);\n"
    "  r1: assert property (@(posedge clk) a[*1:3] ##1 d);\n"
    "  r2: assert property (@(posedge clk) a[=1:3] ##1 d);\n"
    "  r3: assert property (@(posedge clk) a[->2] ##1 d);\n"
    "  r4: assert property (@(posedge clk) a[*2:2] ##1 d);\n"
    "  r5: assert property (@(posedge clk) a[->2:2] ##1 d);\n"
    "  r6: assert property (@(posedge clk) a[=2:2] ##1 d);\n"
    "  r7: assert property (@(posedge clk) a[*1:$] ##1 d);\n"
    "  r8: assert property (@(posedge clk) a[*] ##1 d);\n"
    "  r9: assert property (@(posedge clk) a[+] ##1 d);\n"
    "  rs: assert property (@(posedge clk) (a ##1 b)[*2] ##1 d);\n"
    "  j1: assert property (@(posedge clk) (a ##1 b) intersect (c ##1 d));\n"
    "  j2: assert property (@(posedge clk) ((a ##1 b) and (c ##1 d)) ##1 a);\n"
    "  j3: assert property (@(posedge clk) ((a ##1 b) or (c ##1 d)) ##1 a);\n"
    "  sequence sa; (a ##1 b) and (c ##1 d); endsequence\n"
    "  sequence so; (a ##1 b) or (c ##1 d); endsequence\n"
    "  property pm;\n"
    "    int n;\n"
    "    @(posedge clk) first_match(a ##1 b, n = 1);\n"
    "  endproperty\n"
    "endmodule\n";

class SequenceOperandsOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run(kOperandOrders);
  }

  static std::string Spelling(vpiHandle operand) {
    const int kType = vpi_get(vpiType, operand);
    if (kType == vpiOperation) return "op";
    if (kType == vpiConstant) {
      if (vpi_get(vpiConstType, operand) == vpiUnboundedConst) return "$";
      return std::to_string(IntegerOf(operand));
    }
    const char* name = vpi_get_str(vpiName, operand);
    return name == nullptr ? "" : name;
  }

  static std::vector<std::string> Spelled(vpiHandle op) {
    std::vector<std::string> spelled;
    for (vpiHandle operand : OperandsOf(op)) {
      spelled.push_back(Spelling(operand));
    }
    return spelled;
  }

  struct Expected {
    const char* label;
    int op;
    std::vector<std::string> spelled;
  };

  static void ExpectWhole(const Expected& expected) {
    vpiHandle op = PropertyOf(expected.label);
    ASSERT_NE(op, nullptr) << expected.label;
    EXPECT_EQ(OpOf(op), expected.op) << expected.label;
    EXPECT_EQ(Spelled(op), expected.spelled) << expected.label;
  }

  static void ExpectRepeated(const Expected& expected) {
    const std::vector<vpiHandle> kParts =
        OperandsOf(PropertyOf(expected.label));
    ASSERT_FALSE(kParts.empty()) << expected.label;
    EXPECT_EQ(OpOf(kParts.front()), expected.op) << expected.label;
    EXPECT_EQ(Spelled(kParts.front()), expected.spelled) << expected.label;
  }

  static void ExpectSidesDiffer(vpiHandle op) {
    const std::vector<vpiHandle> kSides = OperandsOf(op);
    ASSERT_EQ(kSides.size(), 2u);
    EXPECT_EQ(Spelled(kSides[0]), (std::vector<std::string>{"a", "b", "1"}));
    EXPECT_EQ(Spelled(kSides[1]), (std::vector<std::string>{"c", "d", "1"}));
  }

  static vpiHandle BodyOf(const char* sequence) {
    return vpi_handle(vpiExpr, Named(vpiSequenceDecl, By("top"), sequence));
  }
};

TEST_F(SequenceOperandsOfARun, ALeadingDelaysRangeFollowsItsSequence) {
  ExpectWhole({"u1", vpiUnaryCycleDelayOp, {"a", "1", "3"}});
}

TEST_F(SequenceOperandsOfARun, ALeadingDelayDropsAnEqualRightBound) {
  ExpectWhole({"u2", vpiUnaryCycleDelayOp, {"a", "2"}});
}

TEST_F(SequenceOperandsOfARun, ALeadingDelaysUnboundedRangeEndsInADollar) {
  ExpectWhole({"u3", vpiUnaryCycleDelayOp, {"a", "1", "$"}});
  ExpectWhole({"u4", vpiUnaryCycleDelayOp, {"a", "0", "$"}});
  ExpectWhole({"u5", vpiUnaryCycleDelayOp, {"a", "1", "$"}});
}

TEST_F(SequenceOperandsOfARun, ABinaryDelayDropsAnEqualRightBound) {
  ExpectWhole({"b1", vpiCycleDelayOp, {"a", "b", "2"}});
}

TEST_F(SequenceOperandsOfARun, ABinaryDelaysUnboundedRangeEndsInADollar) {
  ExpectWhole({"b2", vpiCycleDelayOp, {"a", "b", "1", "$"}});
  ExpectWhole({"b3", vpiCycleDelayOp, {"a", "b", "0", "$"}});
  ExpectWhole({"b4", vpiCycleDelayOp, {"a", "b", "1", "$"}});
}

TEST_F(SequenceOperandsOfARun, ARangedRepetitionTakesBothBounds) {
  ExpectRepeated({"r1", vpiConsecutiveRepeatOp, {"a", "1", "3"}});
  ExpectRepeated({"r2", vpiRepeatOp, {"a", "1", "3"}});
}

TEST_F(SequenceOperandsOfARun, ASingleBoundGotoTakesOneBound) {
  ExpectRepeated({"r3", vpiGotoRepeatOp, {"a", "2"}});
}

TEST_F(SequenceOperandsOfARun, ARepetitionDropsAnEqualRightBound) {
  ExpectRepeated({"r4", vpiConsecutiveRepeatOp, {"a", "2"}});
  ExpectRepeated({"r5", vpiGotoRepeatOp, {"a", "2"}});
  ExpectRepeated({"r6", vpiRepeatOp, {"a", "2"}});
}

TEST_F(SequenceOperandsOfARun, AnUnboundedRepetitionEndsInADollar) {
  ExpectRepeated({"r7", vpiConsecutiveRepeatOp, {"a", "1", "$"}});
  ExpectRepeated({"r8", vpiConsecutiveRepeatOp, {"a", "0", "$"}});
  ExpectRepeated({"r9", vpiConsecutiveRepeatOp, {"a", "1", "$"}});
}

TEST_F(SequenceOperandsOfARun, DISABLED_ARepeatedSequenceIsTheFirstOperand) {
  ExpectRepeated({"rs", vpiConsecutiveRepeatOp, {"op", "2"}});
  const std::vector<vpiHandle> kParts = OperandsOf(PropertyOf("rs"));
  ASSERT_FALSE(kParts.empty());
  const std::vector<vpiHandle> kRepeated = OperandsOf(kParts.front());
  ASSERT_FALSE(kRepeated.empty());
  EXPECT_EQ(Spelled(kRepeated.front()),
            (std::vector<std::string>{"a", "b", "1"}));
}

TEST_F(SequenceOperandsOfARun, AnIntersectTakesItsLeftSideFirst) {
  vpiHandle op = PropertyOf("j1");
  EXPECT_EQ(OpOf(op), vpiIntersectOp);
  ExpectSidesDiffer(op);
}

TEST_F(SequenceOperandsOfARun, DISABLED_AnAndUnderADelayIsASequenceAnd) {
  const std::vector<vpiHandle> kParts = OperandsOf(PropertyOf("j2"));
  ASSERT_FALSE(kParts.empty());
  EXPECT_EQ(OpOf(kParts.front()), vpiCompAndOp);
  ExpectSidesDiffer(kParts.front());
}

TEST_F(SequenceOperandsOfARun, DISABLED_AnOrUnderADelayIsASequenceOr) {
  const std::vector<vpiHandle> kParts = OperandsOf(PropertyOf("j3"));
  ASSERT_FALSE(kParts.empty());
  EXPECT_EQ(OpOf(kParts.front()), vpiCompOrOp);
  ExpectSidesDiffer(kParts.front());
}

TEST_F(SequenceOperandsOfARun, ASequencesBodyAndIsASequenceAnd) {
  vpiHandle body = BodyOf("sa");
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(OpOf(body), vpiCompAndOp);
  ExpectSidesDiffer(body);
}

TEST_F(SequenceOperandsOfARun, ASequencesBodyOrIsASequenceOr) {
  vpiHandle body = BodyOf("so");
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(OpOf(body), vpiCompOrOp);
  ExpectSidesDiffer(body);
}

TEST_F(SequenceOperandsOfARun, DISABLED_AFirstMatchsOperandIsItsSequenceAlone) {
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "pm");
  ASSERT_NE(decl, nullptr);
  vpiHandle matched =
      vpi_handle(vpiPropertyExpr, vpi_handle(vpiPropertySpec, decl));
  ASSERT_NE(matched, nullptr);
  EXPECT_EQ(OpOf(matched), vpiFirstMatchOp);
  EXPECT_EQ(Spelled(matched), (std::vector<std::string>{"op"}));
  const std::vector<vpiHandle> kItems = ObjectsOf(vpiMatchItem, matched);
  ASSERT_EQ(kItems.size(), 1u);
  EXPECT_EQ(vpi_get(vpiType, kItems[0]), vpiAssignment);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiLhs, kItems[0])), "n");
}

}  // namespace
}  // namespace delta
