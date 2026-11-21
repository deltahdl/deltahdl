#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sim_context_types.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_dynamic_ranges.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(ObjectRange, EmptyRangeStandsForDynamicQueueAndAssociativeDimensions) {
  EXPECT_TRUE(VpiDimensionRangeIsEmpty(VpiDimensionKind::kAssoc));
  EXPECT_TRUE(VpiDimensionRangeIsEmpty(VpiDimensionKind::kDynamic));
  EXPECT_TRUE(VpiDimensionRangeIsEmpty(VpiDimensionKind::kQueue));
}

TEST(ObjectRange, FixedDimensionsAreNotEmptyRanges) {
  EXPECT_FALSE(VpiDimensionRangeIsEmpty(VpiDimensionKind::kPacked));
  EXPECT_FALSE(VpiDimensionRangeIsEmpty(VpiDimensionKind::kFixedUnpacked));
}

TEST(ObjectRange, EmptyRangeHasZeroSizeAndNullBounds) {
  VpiObject left;
  VpiObject right;
  VpiRangeDesc range;
  range.empty = true;
  range.left_expr = &left;
  range.right_expr = &right;
  range.size = 7;

  EXPECT_EQ(VpiRangeSize(range), 0);
  EXPECT_EQ(VpiRangeLeftRange(range), nullptr);
  EXPECT_EQ(VpiRangeRightRange(range), nullptr);
}

TEST(ObjectRange, NonEmptyRangeReportsSizeAndBoundExpressions) {
  VpiObject left;
  VpiObject right;
  VpiRangeDesc range;
  range.empty = false;
  range.left_expr = &left;
  range.right_expr = &right;
  range.size = 10;

  EXPECT_EQ(VpiRangeSize(range), 10);
  EXPECT_EQ(VpiRangeLeftRange(range), &left);
  EXPECT_EQ(VpiRangeRightRange(range), &right);
}

TEST(ObjectRange, NonEmptyRangeWithZeroCountStillReportsBounds) {
  VpiObject left;
  VpiObject right;
  VpiRangeDesc range;
  range.empty = false;
  range.left_expr = &left;
  range.right_expr = &right;
  range.size = 0;

  EXPECT_EQ(VpiRangeSize(range), 0);
  EXPECT_EQ(VpiRangeLeftRange(range), &left);
  EXPECT_EQ(VpiRangeRightRange(range), &right);
}

using Ranges = std::vector<std::string>;

class RangesOfARun : public VpiDesignRun {
 protected:
  static std::string BoundOf(vpiHandle bound) {
    return bound == nullptr ? "-" : std::to_string(IntegerOf(bound));
  }

  static std::string RangeText(vpiHandle range) {
    if (range == nullptr) return "(none)";
    return std::to_string(vpi_get(vpiSize, range)) + ":" +
           BoundOf(vpi_handle(vpiLeftRange, range)) + ":" +
           BoundOf(vpi_handle(vpiRightRange, range));
  }

  static Ranges RangesOf(vpiHandle obj) {
    Ranges ranges;
    for (vpiHandle range : ObjectsOf(vpiRange, obj)) {
      ranges.push_back(RangeText(range));
    }
    return ranges;
  }

  static std::string FirstRangeOf(vpiHandle obj) {
    const Ranges kRanges = RangesOf(obj);
    return kRanges.empty() ? "(none)" : kRanges.front();
  }

  static Ranges AllEmpty(const Ranges& ranges) {
    return Ranges(ranges.empty() ? 1 : ranges.size(), "0:-:-");
  }
};

TEST_F(RangesOfARun, ADynamicArraysRangeFollowsItsCurrentSize) {
  Run("module top;\n"
      "  int arr1 []; int empty1 []; int q [$];\n"
      "  initial begin arr1 = new[2]; q = {5, 6, 7}; end\n"
      "endmodule\n");
  EXPECT_EQ(FirstRangeOf(By("top.arr1")), "2:0:1");
  EXPECT_EQ(FirstRangeOf(By("top.q")), "3:0:2");
  EXPECT_EQ(FirstRangeOf(By("top.empty1")), "0:-:-");
  EXPECT_EQ(BoundOf(vpi_handle(vpiRightRange, By("top.arr1"))), "1");
}

TEST_F(RangesOfARun, ARangesSizeAndBoundsAreThoseItsDimensionDeclares) {
  Run("module top;\n"
      "  parameter int W = 6;\n"
      "  logic [W-1:0] pv; logic [0:7] asc; logic [3:3] one;\n"
      "  bit [1:0][0:2] pk; int neg [-2:1]; int cs [4];\n"
      "  int md [1:0][2:4];\n"
      "endmodule\n");
  EXPECT_EQ(RangesOf(By("top.pv")), (Ranges{"6:5:0"}));
  EXPECT_EQ(RangesOf(By("top.asc")), (Ranges{"8:0:7"}));
  EXPECT_EQ(RangesOf(By("top.one")), (Ranges{"1:3:3"}));
  EXPECT_EQ(RangesOf(By("top.pk")), (Ranges{"2:1:0", "3:0:2"}));
  EXPECT_EQ(RangesOf(By("top.neg")), (Ranges{"4:-2:1"}));
  EXPECT_EQ(RangesOf(By("top.cs")), (Ranges{"4:0:3"}));
  EXPECT_EQ(RangesOf(By("top.md")), (Ranges{"2:1:0", "3:2:4"}));
}

TEST_F(RangesOfARun, AVariableOfEveryInstanceScopeHasItsRanges) {
  Run("interface ifc; logic [3:0] ia [1:2]; endinterface\n"
      "program prg; logic [3:0] ra [1:2]; endprogram\n"
      "module top;\n"
      "  ifc i0(); prg p0();\n"
      "  if (1) begin : g logic [3:0] ga [1:2]; end\n"
      "  task t; logic [3:0] ta [1:2]; endtask\n"
      "  function void f; logic [3:0] fa [1:2]; endfunction\n"
      "endmodule\n");
  EXPECT_EQ(RangesOf(By("top.i0.ia")), (Ranges{"2:1:2"}));
  EXPECT_EQ(RangesOf(By("top.p0.ra")), (Ranges{"2:1:2"}));
  EXPECT_EQ(RangesOf(By("top.g.ga")), (Ranges{"2:1:2"}));
  EXPECT_EQ(RangesOf(Named(vpiVariables, By("top.t"), "ta")),
            (Ranges{"2:1:2"}));
  EXPECT_EQ(RangesOf(Named(vpiVariables, By("top.f"), "fa")),
            (Ranges{"2:1:2"}));
}

TEST_F(RangesOfARun, DISABLED_APackageVariableHasItsRanges) {
  Run("package pkg; logic [3:0] pa [1:2]; int pd []; int pq [$]; endpackage\n"
      "module top; endmodule\n");
  for (const char* name : {"pkg::pa", "pkg::pd", "pkg::pq"}) {
    ASSERT_NE(By(name), nullptr) << name;
  }
  EXPECT_EQ(RangesOf(By("pkg::pa")), (Ranges{"2:1:2"}));
  EXPECT_EQ(RangesOf(By("pkg::pd")), (Ranges{"0:-:-"}));
  EXPECT_EQ(RangesOf(By("pkg::pq")), (Ranges{"0:-:-"}));
}

TEST_F(RangesOfARun, DISABLED_AClassPropertyHasItsRanges) {
  Run("module top;\n"
      "  class C; logic [3:0] ca [1:2]; int cd []; int cq [$]; endclass\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  for (const char* name : {"ca", "cd", "cq"}) {
    ASSERT_NE(Named(vpiVariables, defn, name), nullptr) << name;
  }
  EXPECT_EQ(RangesOf(Named(vpiVariables, defn, "ca")), (Ranges{"2:1:2"}));
  EXPECT_EQ(RangesOf(Named(vpiVariables, defn, "cd")), (Ranges{"0:-:-"}));
  EXPECT_EQ(RangesOf(Named(vpiVariables, defn, "cq")), (Ranges{"0:-:-"}));
}

TEST_F(RangesOfARun, ATypespecsRangesReachTheirBounds) {
  Run("module top;\n"
      "  typedef logic [7:4] nib_t; typedef bit [1:0][0:3] pk_t;\n"
      "  typedef int arr_t [0:2][5:4]; typedef int cs_t [3];\n"
      "endmodule\n");
  vpiHandle top = By("top");
  EXPECT_EQ(RangesOf(Named(vpiTypedef, top, "nib_t")), (Ranges{"4:7:4"}));
  EXPECT_EQ(RangesOf(Named(vpiTypedef, top, "pk_t")),
            (Ranges{"2:1:0", "4:0:3"}));
  EXPECT_EQ(RangesOf(Named(vpiTypedef, top, "arr_t")),
            (Ranges{"3:0:2", "2:5:4"}));
  EXPECT_EQ(RangesOf(Named(vpiTypedef, top, "cs_t")), (Ranges{"3:0:2"}));
}

TEST_F(RangesOfARun, DISABLED_ADistValueRangesSizeIsItsValueCount) {
  Run("module top;\n"
      "  class C; rand int x;\n"
      "    constraint c { x dist { [1:3] := 1, [7:10] :/ 2 }; }\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  const std::vector<vpiHandle> kItems =
      ObjectsOf(vpiConstraintItem, Named(vpiConstraint, defn, "c"));
  ASSERT_EQ(kItems.size(), 1u);
  const std::vector<vpiHandle> kEntries = ObjectsOf(vpiDistItem, kItems[0]);
  ASSERT_EQ(kEntries.size(), 2u);
  EXPECT_EQ(RangeText(vpi_handle(vpiValueRange, kEntries[0])), "3:1:3");
  EXPECT_EQ(RangeText(vpi_handle(vpiValueRange, kEntries[1])), "4:7:10");
}

TEST_F(RangesOfARun, AnEmptyDynamicArrayOrQueueHasAnEmptyRange) {
  Run("module top;\n"
      "  int d []; int q [$]; int bq [$:3]; int dd []; int qq [$];\n"
      "  initial begin\n"
      "    dd = new[3]; dd.delete(); qq = {1, 2}; qq.delete();\n"
      "  end\n"
      "endmodule\n");
  for (const char* name : {"top.d", "top.q", "top.bq", "top.dd", "top.qq"}) {
    EXPECT_EQ(RangesOf(By(name)), (Ranges{"0:-:-"})) << name;
  }
}

TEST_F(RangesOfARun, AnAssociativeDimensionsRangeIsAlwaysEmpty) {
  Run("module top;\n"
      "  typedef bit [1:0] k_t;\n"
      "  int as [string]; int ai [int]; int aw [*]; int ak [k_t];\n"
      "  int ae [string];\n"
      "  initial begin\n"
      "    as[\"a\"] = 1; as[\"b\"] = 2; ai[5] = 1; aw[3] = 4; ak[2'd1] = 7;\n"
      "  end\n"
      "endmodule\n");
  for (const char* name : {"top.as", "top.ai", "top.aw", "top.ak", "top.ae"}) {
    EXPECT_EQ(RangesOf(By(name)), (Ranges{"0:-:-"})) << name;
  }
}

TEST_F(RangesOfARun,
       OnlyTheDynamicDimensionOfAnArrayOfAssociativeArraysIsSized) {
  Run("module top;\n"
      "  int arr1 [][string]; int arr0 [][string];\n"
      "  initial begin arr1 = new[2]; arr1[0][\"hello\"] = 5; end\n"
      "endmodule\n");
  EXPECT_EQ(RangesOf(By("top.arr1")), (Ranges{"2:0:1", "0:-:-"}));
  EXPECT_EQ(RangesOf(By("top.arr0")), (Ranges{"0:-:-", "0:-:-"}));
}

TEST_F(RangesOfARun, ATypespecsUnsizedDimensionGivesAnEmptyRange) {
  Run("module top;\n"
      "  typedef bit [1:0] k_t;\n"
      "  typedef int da_t []; typedef int q_t [$]; typedef int bq_t [$:3];\n"
      "  typedef int as_t [string]; typedef int ak_t [k_t];\n"
      "  typedef int aw_t [*]; typedef int mix_t [][string];\n"
      "  int arr1 [][string];\n"
      "  initial begin arr1 = new[2]; arr1[0][\"hello\"] = 5; end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  for (const char* name :
       {"da_t", "q_t", "bq_t", "as_t", "ak_t", "aw_t", "mix_t"}) {
    const Ranges kRanges = RangesOf(Named(vpiTypedef, top, name));
    EXPECT_EQ(kRanges, AllEmpty(kRanges)) << name;
  }
  const Ranges kOfVariable = RangesOf(vpi_handle(vpiTypespec, By("top.arr1")));
  EXPECT_EQ(kOfVariable, AllEmpty(kOfVariable));
}

TEST_F(RangesOfARun, AnEmptyDynamicArrayOfEveryInstanceScopeHasAnEmptyRange) {
  Run("interface ifc; int id []; endinterface\n"
      "program prg; int rq [$]; endprogram\n"
      "module top;\n"
      "  ifc i0(); prg p0();\n"
      "  if (1) begin : g int gd []; end\n"
      "  task t; int td []; endtask\n"
      "  function void f; int fq [$]; endfunction\n"
      "endmodule\n");
  EXPECT_EQ(RangesOf(By("top.i0.id")), (Ranges{"0:-:-"}));
  EXPECT_EQ(RangesOf(By("top.p0.rq")), (Ranges{"0:-:-"}));
  EXPECT_EQ(RangesOf(By("top.g.gd")), (Ranges{"0:-:-"}));
  EXPECT_EQ(RangesOf(Named(vpiVariables, By("top.t"), "td")),
            (Ranges{"0:-:-"}));
  EXPECT_EQ(RangesOf(Named(vpiVariables, By("top.f"), "fq")),
            (Ranges{"0:-:-"}));
}

TEST(ObjectRange, OnlyADynamicArraysFirstRangeFollowsIt) {
  VpiObject loose;
  loose.type = vpiRange;
  EXPECT_EQ(VpiDynamicRangeOf(&loose), nullptr);
  QueueObject store;
  VpiObject array;
  array.queue = &store;
  VpiObject fixed;
  fixed.type = vpiRange;
  fixed.parent = &array;
  array.children = {&fixed};
  EXPECT_EQ(VpiDynamicRangeOf(&array), nullptr);
  VpiObject bound;
  bound.type = vpiConstant;
  VpiObject bare;
  bare.queue = &store;
  bare.children = {&bound};
  EXPECT_EQ(VpiDynamicRangeOf(&bare), nullptr);
}

}  // namespace
}  // namespace delta
