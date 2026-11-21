#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ConstraintRulesOfARun : public VpiDesignRun {
 protected:
  static vpiHandle ConstraintOf(const char* klass, const char* name) {
    return Named(vpiConstraint, Named(vpiClassDefn, By("top"), klass), name);
  }

  static vpiHandle ObjsConstraint(const char* var, const char* name) {
    return Named(vpiConstraint, vpi_handle(vpiClassObj, By(var)), name);
  }

  static vpiHandle FirstOf(int type, vpiHandle ref) {
    const std::vector<vpiHandle> kAll = ObjectsOf(type, ref);
    return kAll.empty() ? nullptr : kAll.front();
  }

  static vpiHandle FirstItem(vpiHandle constraint) {
    return FirstOf(vpiConstraintItem, constraint);
  }

  static std::vector<int> ValuesOf(vpiHandle dist) {
    std::vector<int> values;
    for (vpiHandle entry : ObjectsOf(vpiDistItem, dist)) {
      values.push_back(IntegerOf(vpi_handle(vpiValueRange, entry)));
    }
    return values;
  }

  static void ExpectOwnsItsEntries(vpiHandle dist) {
    ASSERT_NE(dist, nullptr);
    const std::vector<vpiHandle> kEntries = ObjectsOf(vpiDistItem, dist);
    ASSERT_FALSE(kEntries.empty());
    for (vpiHandle entry : kEntries) {
      EXPECT_EQ(VpiObjectOf(vpi_handle(vpiDistribution, entry)),
                VpiObjectOf(dist));
    }
  }

  static std::string FullNameOf(vpiHandle obj) {
    const char* name = vpi_get_str(vpiFullName, obj);
    return name == nullptr ? std::string() : std::string(name);
  }
};

TEST_F(ConstraintRulesOfARun,
       DISABLED_AnIterationFromNullYieldsTheDesignsConstraints) {
  Run("module top;\n"
      "  class C; rand int x;\n"
      "    constraint c { x > 0; }\n"
      "    extern constraint e;\n"
      "    static constraint d { x < 9; }\n"
      "  endclass\n"
      "  constraint C::e { x != 3; }\n"
      "endmodule\n");
  const std::vector<vpiHandle> kAll = ObjectsOf(vpiConstraint, nullptr);
  std::vector<std::string> names;
  for (vpiHandle constraint : kAll) {
    EXPECT_EQ(vpi_get(vpiType, constraint), vpiConstraint);
    names.emplace_back(vpi_get_str(vpiName, constraint));
  }
  std::ranges::sort(names);
  EXPECT_EQ(names, (std::vector<std::string>{"c", "d", "e"}));
}

TEST_F(ConstraintRulesOfARun,
       DISABLED_AWeightlessDistItemIsAnEqualDistribution) {
  Run("module top;\n"
      "  class C; rand int x;\n"
      "    constraint c { x dist { 7, [1:3], 9 :/ 2 }; }\n"
      "  endclass\n"
      "endmodule\n");
  const std::vector<vpiHandle> kEntries =
      ObjectsOf(vpiDistItem, FirstItem(ConstraintOf("C", "c")));
  ASSERT_EQ(kEntries.size(), 3U);
  EXPECT_EQ(vpi_get(vpiDistType, kEntries[0]), vpiEqualDist);
  EXPECT_EQ(vpi_get(vpiDistType, kEntries[1]), vpiEqualDist);
  EXPECT_EQ(vpi_get(vpiDistType, kEntries[2]), vpiDivDist);
}

TEST_F(ConstraintRulesOfARun,
       DISABLED_AnAbsoluteToleranceEntryReachesAValueRange) {
  Run("module top;\n"
      "  class C; rand int x;\n"
      "    constraint c { x dist { [9 +/- 1] := 1, 4 := 2 }; }\n"
      "  endclass\n"
      "endmodule\n");
  const std::vector<vpiHandle> kEntries =
      ObjectsOf(vpiDistItem, FirstItem(ConstraintOf("C", "c")));
  ASSERT_EQ(kEntries.size(), 2U);
  EXPECT_NE(vpi_handle(vpiValueRange, kEntries[0]), nullptr);
  EXPECT_NE(vpi_handle(vpiValueRange, kEntries[1]), nullptr);
}

TEST_F(ConstraintRulesOfARun,
       DISABLED_APercentToleranceEntryReachesAValueRange) {
  Run("module top;\n"
      "  class C; rand int x;\n"
      "    constraint c { x dist { [100 +%- 10] := 1, 4 := 2 }; }\n"
      "  endclass\n"
      "endmodule\n");
  const std::vector<vpiHandle> kEntries =
      ObjectsOf(vpiDistItem, FirstItem(ConstraintOf("C", "c")));
  ASSERT_EQ(kEntries.size(), 2U);
  EXPECT_NE(vpi_handle(vpiValueRange, kEntries[0]), nullptr);
  EXPECT_NE(vpi_handle(vpiValueRange, kEntries[1]), nullptr);
}

TEST_F(ConstraintRulesOfARun, ANonConstantWeightIsReachedAsItsOwnExpression) {
  Run("module top;\n"
      "  class C; rand int x; int w = 3;\n"
      "    constraint c { x dist { 0 := w, 1 := w + 1, 2 := 5 }; }\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  const std::vector<vpiHandle> kEntries =
      ObjectsOf(vpiDistItem, FirstItem(Named(vpiConstraint, defn, "c")));
  ASSERT_EQ(kEntries.size(), 3U);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiWeight, kEntries[0])),
            VpiObjectOf(Named(vpiVariables, defn, "w")));
  vpiHandle sum = vpi_handle(vpiWeight, kEntries[1]);
  ASSERT_NE(sum, nullptr);
  EXPECT_EQ(vpi_get(vpiType, sum), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, sum), vpiAddOp);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiWeight, kEntries[2])), vpiConstant);
}

TEST_F(ConstraintRulesOfARun, AnExternConstraintReportsItsFullName) {
  Run("module top;\n"
      "  class C; rand int x; constraint c { x > 0; } extern constraint e;\n"
      "  endclass\n"
      "  constraint C::e { x != 3; }\n"
      "endmodule\n");
  vpiHandle e = ConstraintOf("C", "e");
  ASSERT_NE(e, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, e), "top.C::e");
  EXPECT_STREQ(vpi_get_str(vpiFullName, ConstraintOf("C", "c")), "top.C::c");
}

TEST_F(ConstraintRulesOfARun, DISABLED_AClassObjsConstraintsReportFullNames) {
  Run("module top;\n"
      "  class B; rand int x; constraint b { x < 9; } endclass\n"
      "  class C extends B; constraint c { x > 0; } endclass\n"
      "  C h = new;\n"
      "endmodule\n");
  vpiHandle c = ObjsConstraint("top.h", "c");
  vpiHandle b = ObjsConstraint("top.h", "b");
  ASSERT_NE(c, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_TRUE(FullNameOf(c).ends_with(".c")) << FullNameOf(c);
  EXPECT_TRUE(FullNameOf(b).ends_with(".b")) << FullNameOf(b);
}

TEST_F(ConstraintRulesOfARun, AStaticConstraintOffThroughOneObjectIsOffInAll) {
  Run("module top;\n"
      "  class C; rand int x;\n"
      "    constraint c { x > 0; }\n"
      "    static constraint s { x != 3; }\n"
      "  endclass\n"
      "  C h = new;\n"
      "  C g = new;\n"
      "  initial begin h.s.constraint_mode(0); h.c.constraint_mode(0); end\n"
      "endmodule\n");
  vpiHandle s = ObjsConstraint("top.g", "s");
  vpiHandle c = ObjsConstraint("top.g", "c");
  ASSERT_NE(s, nullptr);
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(vpi_get(vpiIsConstraintEnabled, s), 0);
  EXPECT_EQ(vpi_get(vpiIsConstraintEnabled, c), 1);
}

TEST_F(ConstraintRulesOfARun, AConstraintTurnedBackOnIsEnabled) {
  Run("module top;\n"
      "  class C; rand int x;\n"
      "    constraint c { x > 0; }\n"
      "    constraint d { x != 3; }\n"
      "  endclass\n"
      "  C h = new;\n"
      "  initial begin\n"
      "    h.c.constraint_mode(0); h.d.constraint_mode(0);\n"
      "    h.c.constraint_mode(1);\n"
      "  end\n"
      "endmodule\n");
  vpiHandle c = ObjsConstraint("top.h", "c");
  vpiHandle d = ObjsConstraint("top.h", "d");
  ASSERT_NE(c, nullptr);
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(vpi_get(vpiIsConstraintEnabled, c), 1);
  EXPECT_EQ(vpi_get(vpiIsConstraintEnabled, d), 0);
}

TEST_F(ConstraintRulesOfARun, AnImplicitPrototypeCompletedOutsideIsExtern) {
  Run("module top;\n"
      "  class C; rand int x; constraint c { x > 0; } constraint e; endclass\n"
      "  constraint C::e { x != 3; }\n"
      "endmodule\n");
  vpiHandle e = ConstraintOf("C", "e");
  ASSERT_NE(e, nullptr);
  EXPECT_EQ(vpi_get(vpiAccessType, e), vpiExternAcc);
  EXPECT_EQ(vpi_get(vpiAccessType, ConstraintOf("C", "c")), 0);
}

TEST_F(ConstraintRulesOfARun, AnExternStaticPrototypeIsExtern) {
  Run("module top;\n"
      "  class C; rand int x; static constraint d { x < 9; }\n"
      "    extern static constraint e;\n"
      "  endclass\n"
      "  static constraint C::e { x != 3; }\n"
      "endmodule\n");
  vpiHandle e = ConstraintOf("C", "e");
  ASSERT_NE(e, nullptr);
  EXPECT_EQ(vpi_get(vpiAccessType, e), vpiExternAcc);
  EXPECT_EQ(vpi_get(vpiAccessType, ConstraintOf("C", "d")), 0);
}

TEST_F(ConstraintRulesOfARun, AClassObjsExternConstraintIsExtern) {
  Run("module top;\n"
      "  class C; rand int x; constraint c { x > 0; } extern constraint e;\n"
      "  endclass\n"
      "  constraint C::e { x != 3; }\n"
      "  C h = new;\n"
      "endmodule\n");
  vpiHandle e = ObjsConstraint("top.h", "e");
  vpiHandle c = ObjsConstraint("top.h", "c");
  ASSERT_NE(e, nullptr);
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(vpi_get(vpiAccessType, e), vpiExternAcc);
  EXPECT_EQ(vpi_get(vpiAccessType, c), 0);
}

TEST_F(ConstraintRulesOfARun,
       DISABLED_AnUncompletedImplicitPrototypeIsNotExtern) {
  Run("module top;\n"
      "  class C; rand int x; constraint e; endclass\n"
      "endmodule\n");
  vpiHandle e = ConstraintOf("C", "e");
  ASSERT_NE(e, nullptr);
  EXPECT_EQ(vpi_get(vpiAccessType, e), 0);
}

TEST_F(ConstraintRulesOfARun, AnExternStaticConstraintIsNotAutomatic) {
  Run("module top;\n"
      "  class C; rand int x; extern constraint a;\n"
      "    extern static constraint e;\n"
      "  endclass\n"
      "  constraint C::a { x > 0; }\n"
      "  static constraint C::e { x != 3; }\n"
      "endmodule\n");
  vpiHandle e = ConstraintOf("C", "e");
  vpiHandle a = ConstraintOf("C", "a");
  ASSERT_NE(e, nullptr);
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(vpi_get(vpiAutomatic, e), 0);
  EXPECT_EQ(vpi_get(vpiAutomatic, a), 1);
}

TEST_F(ConstraintRulesOfARun, AClassObjsStaticConstraintIsNotAutomatic) {
  Run("module top;\n"
      "  class C; rand int x;\n"
      "    constraint c { x > 0; }\n"
      "    static constraint s { x != 3; }\n"
      "  endclass\n"
      "  C h = new;\n"
      "endmodule\n");
  vpiHandle s = ObjsConstraint("top.h", "s");
  vpiHandle c = ObjsConstraint("top.h", "c");
  ASSERT_NE(s, nullptr);
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(vpi_get(vpiAutomatic, s), 0);
  EXPECT_EQ(vpi_get(vpiAutomatic, c), 1);
}

TEST_F(ConstraintRulesOfARun, InterleavedItemsComeInTheOrderWritten) {
  Run("module top;\n"
      "  class C; rand int x, y;\n"
      "    constraint c {\n"
      "      x < 5; solve x before y; y dist { 1 := 1, 2 := 2 }; y != 3;\n"
      "    }\n"
      "  endclass\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiConstraintItem, ConstraintOf("C", "c")),
            (std::vector<int>{vpiOperation, vpiConstraintOrdering,
                              vpiDistribution, vpiOperation}));
}

TEST_F(ConstraintRulesOfARun, DISABLED_AClassObjsConstraintsAreNotVirtual) {
  Run("module top;\n"
      "  virtual class A; rand int x; pure constraint p; endclass\n"
      "  class C extends A; constraint p { x > 0; } constraint q { x < 9; }\n"
      "  endclass\n"
      "  C h = new;\n"
      "endmodule\n");
  const std::vector<vpiHandle> kAll =
      ObjectsOf(vpiConstraint, vpi_handle(vpiClassObj, By("top.h")));
  ASSERT_GE(kAll.size(), 2U);
  for (vpiHandle constraint : kAll) {
    EXPECT_EQ(vpi_get(vpiVirtual, constraint), 0)
        << vpi_get_str(vpiName, constraint);
  }
  EXPECT_NE(ObjsConstraint("top.h", "p"), nullptr);
  EXPECT_EQ(vpi_get(vpiVirtual, ConstraintOf("A", "p")), 1);
}

TEST_F(ConstraintRulesOfARun, ADistributionInAnImplicationReachesItsParts) {
  Run("module top;\n"
      "  class C; rand int x; rand bit b;\n"
      "    constraint c { b -> x dist { 5 := 1, 2 := 3 }; }\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  vpiHandle implication = FirstItem(Named(vpiConstraint, defn, "c"));
  ASSERT_NE(implication, nullptr);
  const std::vector<vpiHandle> kBody =
      ObjectsOf(vpiConstraintExpr, implication);
  ASSERT_EQ(kBody.size(), 1U);
  EXPECT_EQ(vpi_get(vpiType, kBody[0]), vpiDistribution);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, kBody[0])),
            VpiObjectOf(Named(vpiVariables, defn, "x")));
  EXPECT_EQ(ValuesOf(kBody[0]), (std::vector<int>{5, 2}));
}

TEST_F(ConstraintRulesOfARun, DistributionsInConstrIfBranchesReachTheirParts) {
  Run("module top;\n"
      "  class C; rand int x, y; rand bit b;\n"
      "    constraint c {\n"
      "      if (b) x dist { 5 := 1, 2 := 3 };\n"
      "      if (b) x dist { 4 := 1 }; else y dist { 8 := 1, 6 := 2 };\n"
      "    }\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  const std::vector<vpiHandle> kItems =
      ObjectsOf(vpiConstraintItem, Named(vpiConstraint, defn, "c"));
  ASSERT_EQ(kItems.size(), 2U);
  const std::vector<vpiHandle> kThen = ObjectsOf(vpiConstraintExpr, kItems[0]);
  ASSERT_EQ(kThen.size(), 1U);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, kThen[0])),
            VpiObjectOf(Named(vpiVariables, defn, "x")));
  EXPECT_EQ(ValuesOf(kThen[0]), (std::vector<int>{5, 2}));
  const std::vector<vpiHandle> kElse = ObjectsOf(vpiElseConst, kItems[1]);
  ASSERT_EQ(kElse.size(), 1U);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, kElse[0])),
            VpiObjectOf(Named(vpiVariables, defn, "y")));
  EXPECT_EQ(ValuesOf(kElse[0]), (std::vector<int>{8, 6}));
}

TEST_F(ConstraintRulesOfARun, AClassObjsDistributionReachesItsParts) {
  Run("module top;\n"
      "  class C; rand int x; constraint c { x dist { 5 := 1, 2 := 3 }; }\n"
      "  endclass\n"
      "  C h = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.h"));
  vpiHandle dist = FirstItem(Named(vpiConstraint, obj, "c"));
  ASSERT_NE(dist, nullptr);
  EXPECT_EQ(vpi_get(vpiType, dist), vpiDistribution);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, dist)),
            VpiObjectOf(Named(vpiVariables, obj, "x")));
  EXPECT_EQ(ValuesOf(dist), (std::vector<int>{5, 2}));
}

TEST_F(ConstraintRulesOfARun, EveryDistItemReachesItsDistribution) {
  Run("module top;\n"
      "  class C; rand int x, y; rand bit b;\n"
      "    constraint c {\n"
      "      x dist { 5 := 1, 2 := 3 };\n"
      "      b -> y dist { 1 := 1 };\n"
      "      if (b) x dist { 4 := 1 }; else y dist { 8 := 1 };\n"
      "    }\n"
      "  endclass\n"
      "  C h = new;\n"
      "endmodule\n");
  const std::vector<vpiHandle> kItems =
      ObjectsOf(vpiConstraintItem, ConstraintOf("C", "c"));
  ASSERT_EQ(kItems.size(), 3U);
  ExpectOwnsItsEntries(kItems[0]);
  ExpectOwnsItsEntries(FirstOf(vpiConstraintExpr, kItems[1]));
  ExpectOwnsItsEntries(FirstOf(vpiConstraintExpr, kItems[2]));
  ExpectOwnsItsEntries(FirstOf(vpiElseConst, kItems[2]));
  ExpectOwnsItsEntries(FirstItem(ObjsConstraint("top.h", "c")));
}

TEST_F(ConstraintRulesOfARun, AnOrderingSolvesEveryNameAfterBefore) {
  Run("module top;\n"
      "  class C; rand int a, x, y, z;\n"
      "    constraint c { solve a before z, x, y; }\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  vpiHandle ordering = FirstItem(Named(vpiConstraint, defn, "c"));
  ASSERT_NE(ordering, nullptr);
  const std::vector<vpiHandle> kAfter = ObjectsOf(vpiSolveAfter, ordering);
  ASSERT_EQ(kAfter.size(), 3U);
  EXPECT_EQ(VpiObjectOf(kAfter[0]),
            VpiObjectOf(Named(vpiVariables, defn, "z")));
  EXPECT_EQ(VpiObjectOf(kAfter[1]),
            VpiObjectOf(Named(vpiVariables, defn, "x")));
  EXPECT_EQ(VpiObjectOf(kAfter[2]),
            VpiObjectOf(Named(vpiVariables, defn, "y")));
}

TEST_F(ConstraintRulesOfARun, AClassObjsOrderingReachesTheObjectsVariables) {
  Run("module top;\n"
      "  class C; rand int x, y; constraint c { solve x before y; } endclass\n"
      "  C h = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.h"));
  vpiHandle ordering = FirstItem(Named(vpiConstraint, obj, "c"));
  ASSERT_NE(ordering, nullptr);
  const std::vector<vpiHandle> kBefore = ObjectsOf(vpiSolveBefore, ordering);
  const std::vector<vpiHandle> kAfter = ObjectsOf(vpiSolveAfter, ordering);
  ASSERT_EQ(kBefore.size(), 1U);
  ASSERT_EQ(kAfter.size(), 1U);
  EXPECT_EQ(VpiObjectOf(kBefore[0]),
            VpiObjectOf(Named(vpiVariables, obj, "x")));
  EXPECT_EQ(VpiObjectOf(kAfter[0]), VpiObjectOf(Named(vpiVariables, obj, "y")));
}

TEST_F(ConstraintRulesOfARun, AClassObjsConstraintHoldsItsOrderingInPlace) {
  Run("module top;\n"
      "  class C; rand int x, y;\n"
      "    constraint c { x > 0; solve x before y; y < 9; }\n"
      "  endclass\n"
      "  C h = new;\n"
      "endmodule\n");
  EXPECT_EQ(
      KindsOf(vpiConstraintItem, ObjsConstraint("top.h", "c")),
      (std::vector<int>{vpiOperation, vpiConstraintOrdering, vpiOperation}));
}

TEST_F(ConstraintRulesOfARun, AnExternBlocksOrderingAndDistributionAreItems) {
  Run("module top;\n"
      "  class C; rand int x, y; extern constraint c; endclass\n"
      "  constraint C::c { solve x before y; y dist { 1 := 1 }; x > 0; }\n"
      "endmodule\n");
  EXPECT_EQ(
      KindsOf(vpiConstraintItem, ConstraintOf("C", "c")),
      (std::vector<int>{vpiConstraintOrdering, vpiDistribution, vpiOperation}));
}

}  // namespace
}  // namespace delta
