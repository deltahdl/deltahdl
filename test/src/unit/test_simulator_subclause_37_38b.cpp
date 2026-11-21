#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ConstraintRulesOfARun : public VpiDesignRun {
 protected:
  static vpiHandle Defn(const char* name) {
    return Named(vpiClassDefn, By("top"), name);
  }

  static vpiHandle Obj(const char* name) {
    return vpi_handle(vpiClassObj, By(name));
  }

  static std::vector<vpiHandle> Items(vpiHandle holder, const char* name) {
    return ObjectsOf(vpiConstraintItem, Named(vpiConstraint, holder, name));
  }

  static std::vector<vpiHandle> InlineItems() {
    std::vector<vpiHandle> calls = ObjectsOf(vpiStmt, By("top.blk"));
    if (calls.empty()) return {};
    return ObjectsOf(vpiConstraintItem, vpi_handle(vpiWith, calls[0]));
  }

  static std::vector<int> PropertyOf(int property,
                                     const std::vector<vpiHandle>& objects) {
    std::vector<int> values;
    values.reserve(objects.size());
    for (vpiHandle obj : objects) values.push_back(vpi_get(property, obj));
    return values;
  }

  static std::vector<int> TypesOf(const std::vector<vpiHandle>& objects) {
    return PropertyOf(vpiType, objects);
  }

  static std::vector<int> OpTypesOf(const std::vector<vpiHandle>& objects) {
    return PropertyOf(vpiOpType, objects);
  }

  static std::vector<int> SoftsOf(const std::vector<vpiHandle>& objects) {
    return PropertyOf(vpiSoft, objects);
  }

  static std::vector<int> EveryKind() {
    return {vpiImplication,   vpiConstrIf,     vpiConstrIfElse,
            vpiConstrForEach, vpiDistribution, vpiSoftDisable};
  }

  static std::string FirstOperandName(vpiHandle op) {
    const std::vector<vpiHandle> kOperands = ObjectsOf(vpiOperand, op);
    if (kOperands.empty()) return "";
    const char* name = vpi_get_str(vpiName, kOperands[0]);
    return name == nullptr ? "" : name;
  }

  static bool Same(vpiHandle a, vpiHandle b) {
    return a != nullptr && b != nullptr && vpi_compare_objects(a, b) == 1;
  }
};

constexpr const char* kSoft =
    "module top;\n"
    "  class C; rand int x, y; rand bit b; rand int q[3];\n"
    "    constraint c {\n"
    "      soft b;\n"
    "      soft x dist { 1 := 2, [3:5] :/ 1 };\n"
    "      x dist { 1 := 1, [3:5] :/ 1 };\n"
    "      if (b) { soft x > 0; y > 0; }\n"
    "      if (b) y > 1; else { soft x < 4; y < 7; }\n"
    "      x > 1 -> { soft y < 3; y > -9; }\n"
    "      foreach (q[i]) { soft q[i] < 9; q[i] > 0; }\n"
    "    }\n"
    "  endclass\n"
    "  C h = new;\n"
    "  initial begin : blk\n"
    "    void'(h.randomize() with { soft x > 0; x < 9; });\n"
    "  end\n"
    "endmodule\n";

TEST_F(ConstraintRulesOfARun, DISABLED_ASoftNameStandingAloneIsSoft) {
  Run(kSoft);
  const std::vector<vpiHandle> kItems = Items(Defn("C"), "c");
  ASSERT_EQ(kItems.size(), 7u);
  EXPECT_EQ(vpi_get(vpiSoft, kItems[0]), 1);
}

TEST_F(ConstraintRulesOfARun,
       DISABLED_ASoftDistributionIsSoftAndAPlainOneIsNot) {
  Run(kSoft);
  const std::vector<vpiHandle> kItems = Items(Defn("C"), "c");
  ASSERT_EQ(kItems.size(), 7u);
  EXPECT_EQ(TypesOf({kItems[1], kItems[2]}),
            (std::vector<int>{vpiDistribution, vpiDistribution}));
  EXPECT_EQ(SoftsOf({kItems[1], kItems[2]}), (std::vector<int>{1, 0}));
}

TEST_F(ConstraintRulesOfARun, ASoftExpressionInEveryContainersBodyIsSoft) {
  Run(kSoft);
  const std::vector<vpiHandle> kItems = Items(Defn("C"), "c");
  ASSERT_EQ(kItems.size(), 7u);
  const std::vector<int> kSoftThenPlain = {1, 0};
  EXPECT_EQ(SoftsOf(ObjectsOf(vpiConstraintExpr, kItems[3])), kSoftThenPlain);
  EXPECT_EQ(SoftsOf(ObjectsOf(vpiElseConst, kItems[4])), kSoftThenPlain);
  EXPECT_EQ(SoftsOf(ObjectsOf(vpiConstraintExpr, kItems[5])), kSoftThenPlain);
  EXPECT_EQ(SoftsOf(ObjectsOf(vpiConstraintExpr, kItems[6])), kSoftThenPlain);
}

TEST_F(ConstraintRulesOfARun, ASoftExpressionOfAnInlineBlockIsSoft) {
  Run(kSoft);
  EXPECT_EQ(SoftsOf(InlineItems()), (std::vector<int>{1, 0}));
}

TEST_F(ConstraintRulesOfARun, ASoftExpressionOfAClassObjIsSoft) {
  Run(kSoft);
  vpiHandle obj = Obj("top.h");
  ASSERT_NE(obj, nullptr);
  const std::vector<vpiHandle> kItems = Items(obj, "c");
  ASSERT_EQ(kItems.size(), 7u);
  EXPECT_EQ(SoftsOf(ObjectsOf(vpiConstraintExpr, kItems[3])),
            (std::vector<int>{1, 0}));
}

constexpr const char* kLoops =
    "module top;\n"
    "  class B; rand int barr[2]; endclass\n"
    "  class D; rand int arr[3]; endclass\n"
    "  class C extends B;\n"
    "    rand int g[2][2][2], d[], u[$], m[int]; rand D h;\n"
    "    constraint c {\n"
    "      foreach (g[i, j]) g[i][j][0] > 0;\n"
    "      foreach (g[i, , k]) g[i][0][k] > 0;\n"
    "      foreach (g[i, ]) g[i][0][0] > 0;\n"
    "      foreach (d[n]) d[n] > 0;\n"
    "      foreach (u[n]) u[n] > 0;\n"
    "      foreach (m[n]) m[n] > 0;\n"
    "      foreach (h.arr[n]) h.arr[n] > 0;\n"
    "      foreach (barr[n]) barr[n] > 0;\n"
    "    }\n"
    "  endclass\n"
    "  C k = new;\n"
    "endmodule\n";

TEST_F(ConstraintRulesOfARun, NamedIndicesIterateAsVariablesLeftToRight) {
  Run(kLoops);
  const std::vector<vpiHandle> kItems = Items(Defn("C"), "c");
  ASSERT_EQ(kItems.size(), 8u);
  const std::vector<vpiHandle> kIndices = ObjectsOf(vpiLoopVars, kItems[0]);
  ASSERT_EQ(kIndices.size(), 2u);
  EXPECT_STREQ(vpi_get_str(vpiName, kIndices[0]), "i");
  EXPECT_STREQ(vpi_get_str(vpiName, kIndices[1]), "j");
  EXPECT_EQ(TypesOf(kIndices), (std::vector<int>{vpiIntVar, vpiIntVar}));
}

TEST_F(ConstraintRulesOfARun, ASkippedIndexIterateAsANullOpInItsPlace) {
  Run(kLoops);
  const std::vector<vpiHandle> kItems = Items(Defn("C"), "c");
  ASSERT_EQ(kItems.size(), 8u);
  const std::vector<vpiHandle> kMiddle = ObjectsOf(vpiLoopVars, kItems[1]);
  ASSERT_EQ(kMiddle.size(), 3u);
  EXPECT_STREQ(vpi_get_str(vpiName, kMiddle[0]), "i");
  EXPECT_EQ(vpi_get(vpiType, kMiddle[1]), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, kMiddle[1]), vpiNullOp);
  EXPECT_STREQ(vpi_get_str(vpiName, kMiddle[2]), "k");
  const std::vector<vpiHandle> kTrailing = ObjectsOf(vpiLoopVars, kItems[2]);
  ASSERT_EQ(kTrailing.size(), 2u);
  EXPECT_STREQ(vpi_get_str(vpiName, kTrailing[0]), "i");
  EXPECT_EQ(vpi_get(vpiOpType, kTrailing[1]), vpiNullOp);
}

TEST_F(ConstraintRulesOfARun, AForeachOverEveryKindOfArrayReachesIt) {
  Run(kLoops);
  vpiHandle defn = Defn("C");
  const std::vector<vpiHandle> kItems = Items(defn, "c");
  ASSERT_EQ(kItems.size(), 8u);
  EXPECT_TRUE(Same(vpi_handle(vpiVariables, kItems[3]),
                   Named(vpiVariables, defn, "d")));
  EXPECT_TRUE(Same(vpi_handle(vpiVariables, kItems[4]),
                   Named(vpiVariables, defn, "u")));
  EXPECT_TRUE(Same(vpi_handle(vpiVariables, kItems[5]),
                   Named(vpiVariables, defn, "m")));
}

TEST_F(ConstraintRulesOfARun, DISABLED_AForeachOverAMembersArrayReachesIt) {
  Run(kLoops);
  const std::vector<vpiHandle> kItems = Items(Defn("C"), "c");
  ASSERT_EQ(kItems.size(), 8u);
  EXPECT_TRUE(Same(vpi_handle(vpiVariables, kItems[6]),
                   Named(vpiVariables, Defn("D"), "arr")));
}

TEST_F(ConstraintRulesOfARun, AForeachOverAnInheritedArrayReachesIt) {
  Run(kLoops);
  const std::vector<vpiHandle> kItems = Items(Defn("C"), "c");
  ASSERT_EQ(kItems.size(), 8u);
  EXPECT_TRUE(Same(vpi_handle(vpiVariables, kItems[7]),
                   Named(vpiVariables, Defn("B"), "barr")));
}

TEST_F(ConstraintRulesOfARun, AClassObjsForeachReachesItsOwnArray) {
  Run(kLoops);
  vpiHandle obj = Obj("top.k");
  ASSERT_NE(obj, nullptr);
  const std::vector<vpiHandle> kItems = Items(obj, "c");
  ASSERT_EQ(kItems.size(), 8u);
  EXPECT_EQ(vpi_get(vpiType, kItems[3]), vpiConstrForEach);
  vpiHandle array = vpi_handle(vpiVariables, kItems[3]);
  EXPECT_TRUE(Same(array, Named(vpiVariables, obj, "d")));
  EXPECT_FALSE(Same(array, Named(vpiVariables, Defn("C"), "d")));
}

constexpr const char* kBodies =
    "module top;\n"
    "  class C; rand int x, y; rand bit a, b; rand int q[3], g[2][2];\n"
    "    constraint c {\n"
    "      if (b) x > 0; else { x < 2; y > 3; y < 7; }\n"
    "      if (a) x > 1; else if (b) y > 1; else x < 0;\n"
    "      if (y > 2) x > 2; else x < 2;\n"
    "      x dist { 1 := 1, 2 := 1 };\n"
    "      foreach (q[i]) q[i] < 9;\n"
    "      y < 9;\n"
    "      soft b;\n"
    "      if (b) y > 1;\n"
    "      x > 0 -> { y > 1; y < 5; }\n"
    "      if (b) { x < 3; y != 4; }\n"
    "      if (b) { x > 2; y > 2; } else x < 0;\n"
    "      foreach (q[i]) { q[i] > 0; q[i] < 9; }\n"
    "      foreach (g[i]) { foreach (q[j]) g[i][j % 2] > 0; g[i][0] < 5; }\n"
    "      if (b) { x < 5 -> y > 0; foreach (q[i]) q[i] < 9; if (a) x > 1; }\n"
    "    }\n"
    "  endclass\n"
    "endmodule\n";

TEST_F(ConstraintRulesOfARun, AnElseBlockYieldsEveryExpressionInOrder) {
  Run(kBodies);
  const std::vector<vpiHandle> kItems = Items(Defn("C"), "c");
  ASSERT_EQ(kItems.size(), 14u);
  const std::vector<vpiHandle> kElse = ObjectsOf(vpiElseConst, kItems[0]);
  ASSERT_EQ(kElse.size(), 3u);
  EXPECT_EQ(TypesOf(kElse),
            (std::vector<int>{vpiOperation, vpiOperation, vpiOperation}));
  EXPECT_EQ(OpTypesOf(kElse), (std::vector<int>{vpiLtOp, vpiGtOp, vpiLtOp}));
  EXPECT_EQ(FirstOperandName(kElse[0]), "x");
  EXPECT_EQ(FirstOperandName(kElse[1]), "y");
}

TEST_F(ConstraintRulesOfARun, AnElseIfChainNestsAnIfElseInTheElse) {
  Run(kBodies);
  const std::vector<vpiHandle> kItems = Items(Defn("C"), "c");
  ASSERT_EQ(kItems.size(), 14u);
  const std::vector<vpiHandle> kElse = ObjectsOf(vpiElseConst, kItems[1]);
  ASSERT_EQ(kElse.size(), 1u);
  vpiHandle inner = kElse[0];
  EXPECT_EQ(vpi_get(vpiType, inner), vpiConstrIfElse);
  vpiHandle guard = vpi_handle(vpiCondition, inner);
  ASSERT_NE(guard, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, guard), "b");
  const std::vector<vpiHandle> kThen = ObjectsOf(vpiConstraintExpr, inner);
  ASSERT_EQ(kThen.size(), 1u);
  EXPECT_EQ(FirstOperandName(kThen[0]), "y");
  const std::vector<vpiHandle> kLast = ObjectsOf(vpiElseConst, inner);
  ASSERT_EQ(kLast.size(), 1u);
  EXPECT_EQ(vpi_get(vpiOpType, kLast[0]), vpiLtOp);
}

TEST_F(ConstraintRulesOfARun, OnlyTheGuardedKindsReachACondition) {
  Run(kBodies);
  const std::vector<vpiHandle> kItems = Items(Defn("C"), "c");
  ASSERT_EQ(kItems.size(), 14u);
  vpiHandle guard = vpi_handle(vpiCondition, kItems[2]);
  ASSERT_NE(guard, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, guard), vpiGtOp);
  EXPECT_EQ(FirstOperandName(guard), "y");
  for (const int kIndex : {3, 4, 5, 6}) {
    EXPECT_EQ(vpi_handle(vpiCondition, kItems[kIndex]), nullptr) << kIndex;
  }
}

TEST_F(ConstraintRulesOfARun, EveryContainersBodyComesBackInOrder) {
  Run(kBodies);
  const std::vector<vpiHandle> kItems = Items(Defn("C"), "c");
  ASSERT_EQ(kItems.size(), 14u);
  EXPECT_EQ(OpTypesOf(ObjectsOf(vpiConstraintExpr, kItems[7])),
            (std::vector<int>{vpiGtOp}));
  EXPECT_EQ(OpTypesOf(ObjectsOf(vpiConstraintExpr, kItems[8])),
            (std::vector<int>{vpiGtOp, vpiLtOp}));
  EXPECT_EQ(OpTypesOf(ObjectsOf(vpiConstraintExpr, kItems[9])),
            (std::vector<int>{vpiLtOp, vpiNeqOp}));
  EXPECT_EQ(OpTypesOf(ObjectsOf(vpiConstraintExpr, kItems[10])),
            (std::vector<int>{vpiGtOp, vpiGtOp}));
  const std::vector<vpiHandle> kThen = ObjectsOf(vpiConstraintExpr, kItems[10]);
  ASSERT_EQ(kThen.size(), 2u);
  EXPECT_EQ(FirstOperandName(kThen[0]), "x");
  EXPECT_EQ(FirstOperandName(kThen[1]), "y");
  EXPECT_EQ(OpTypesOf(ObjectsOf(vpiConstraintExpr, kItems[11])),
            (std::vector<int>{vpiGtOp, vpiLtOp}));
}

TEST_F(ConstraintRulesOfARun, ANestedContainerIsItsOwnKindInTheBody) {
  Run(kBodies);
  const std::vector<vpiHandle> kItems = Items(Defn("C"), "c");
  ASSERT_EQ(kItems.size(), 14u);
  EXPECT_EQ(TypesOf(ObjectsOf(vpiConstraintExpr, kItems[12])),
            (std::vector<int>{vpiConstrForEach, vpiOperation}));
  EXPECT_EQ(TypesOf(ObjectsOf(vpiConstraintExpr, kItems[13])),
            (std::vector<int>{vpiImplication, vpiConstrForEach, vpiConstrIf}));
}

constexpr const char* kDisables =
    "module top;\n"
    "  class B; rand int y; endclass\n"
    "  class C extends B; rand int x;\n"
    "    constraint c { soft y > 0; soft x > 0; disable soft y; disable soft "
    "x; }\n"
    "  endclass\n"
    "  C k = new;\n"
    "  initial begin : blk\n"
    "    void'(k.randomize() with { disable soft x; });\n"
    "  end\n"
    "endmodule\n";

TEST_F(ConstraintRulesOfARun, ASoftDisableOfAnInheritedPropertyReachesIt) {
  Run(kDisables);
  const std::vector<vpiHandle> kItems = Items(Defn("C"), "c");
  ASSERT_EQ(kItems.size(), 4u);
  EXPECT_EQ(vpi_get(vpiType, kItems[2]), vpiSoftDisable);
  EXPECT_TRUE(Same(vpi_handle(vpiExpr, kItems[2]),
                   Named(vpiVariables, Defn("B"), "y")));
}

TEST_F(ConstraintRulesOfARun, AClassObjsSoftDisableReachesItsOwnProperty) {
  Run(kDisables);
  vpiHandle obj = Obj("top.k");
  ASSERT_NE(obj, nullptr);
  const std::vector<vpiHandle> kItems = Items(obj, "c");
  ASSERT_EQ(kItems.size(), 4u);
  EXPECT_TRUE(
      Same(vpi_handle(vpiExpr, kItems[3]), Named(vpiVariables, obj, "x")));
}

TEST_F(ConstraintRulesOfARun, AnInlineSoftDisableReachesTheClassProperty) {
  Run(kDisables);
  const std::vector<vpiHandle> kItems = InlineItems();
  ASSERT_EQ(kItems.size(), 1u);
  EXPECT_EQ(vpi_get(vpiType, kItems[0]), vpiSoftDisable);
  EXPECT_TRUE(Same(vpi_handle(vpiExpr, kItems[0]),
                   Named(vpiVariables, Defn("C"), "x")));
}

TEST_F(ConstraintRulesOfARun, ASoftDisableOfAMemberReachesAReferenceToIt) {
  Run("module top;\n"
      "  class D; rand int x; endclass\n"
      "  class C; rand D h;\n"
      "    constraint c { soft h.x > 0; disable soft h.x; }\n"
      "  endclass\n"
      "endmodule\n");
  const std::vector<vpiHandle> kItems = Items(Defn("C"), "c");
  ASSERT_EQ(kItems.size(), 2u);
  vpiHandle target = vpi_handle(vpiExpr, kItems[1]);
  ASSERT_NE(target, nullptr);
  EXPECT_EQ(vpi_get(vpiType, target), vpiRefObj);
}

constexpr const char* kKinds =
    "module top;\n"
    "  class C; rand int x, y; rand bit b; rand int q[3];\n"
    "    constraint c {\n"
    "      x > 0 -> y > 0; if (b) y > 1; if (b) x > 1; else x < 0;\n"
    "      foreach (q[i]) q[i] < 9; x dist { 1 := 1, 2 := 1 };\n"
    "      disable soft x;\n"
    "    }\n"
    "    extern constraint e;\n"
    "  endclass\n"
    "  constraint C::e {\n"
    "    x > 0 -> y > 0; if (b) y > 1; if (b) x > 1; else x < 0;\n"
    "    foreach (q[i]) q[i] < 9; x dist { 1 := 1, 2 := 1 };\n"
    "    disable soft x;\n"
    "  }\n"
    "  C k = new;\n"
    "  initial begin : blk\n"
    "    void'(k.randomize() with {\n"
    "      x > 0 -> y > 0; if (b) y > 1; if (b) x > 1; else x < 0;\n"
    "      foreach (q[i]) q[i] < 9; x dist { 1 := 1, 2 := 1 };\n"
    "      disable soft x;\n"
    "    });\n"
    "  end\n"
    "endmodule\n";

TEST_F(ConstraintRulesOfARun, AnOutOfBlockConstraintsItemsAreTheirKinds) {
  Run(kKinds);
  EXPECT_EQ(TypesOf(Items(Defn("C"), "e")), EveryKind());
}

TEST_F(ConstraintRulesOfARun, AClassObjsConstraintItemsAreTheirKinds) {
  Run(kKinds);
  vpiHandle obj = Obj("top.k");
  ASSERT_NE(obj, nullptr);
  EXPECT_EQ(TypesOf(Items(obj, "c")), EveryKind());
}

TEST_F(ConstraintRulesOfARun, AnInlineBlocksItemsAreTheirKinds) {
  Run(kKinds);
  EXPECT_EQ(TypesOf(InlineItems()), EveryKind());
}

}  // namespace
}  // namespace delta
