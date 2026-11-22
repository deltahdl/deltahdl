#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr const char* kForms =
    "module sub; event e; endmodule\n"
    "module top; parameter P = 4; bit c, d, en; event e; int a, b, n = 2;\n"
    "  logic [3:0] v; integer k; sub u();\n"
    "  function int f; return 2; endfunction\n"
    "  initial a = repeat (3) @(posedge c) b;\n"
    "  initial a = repeat (3) @(negedge c) b;\n"
    "  initial a = repeat (3) @(edge c) b;\n"
    "  initial a = repeat (3) @(c or d) b;\n"
    "  initial a = repeat (3) @(c, d) b;\n"
    "  initial a = repeat (3) @e b;\n"
    "  initial a = repeat (3) @(u.e) b;\n"
    "  initial a = repeat (3) @* b;\n"
    "  initial a = repeat (3) @(*) b;\n"
    "  initial a = repeat (3) @(c iff en) b;\n"
    "  initial a <= repeat (n) @(posedge c) b;\n"
    "  initial a = repeat (n) @(c) b;\n"
    "  initial a = repeat (P) @(c) b;\n"
    "  initial a = repeat (v[0]) @(c) b;\n"
    "  initial a = repeat (v[1:0]) @(c) b;\n"
    "  initial a = repeat (n + 1) @(c) b;\n"
    "  initial a = repeat (f()) @(c) b;\n"
    "  initial a = repeat (k[0]) @(c) b;\n"
    "  initial #100 $finish;\n"
    "endmodule\n";

class RepeatControlsEverywhere : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run(kForms);
  }

  static vpiHandle RepeatOf(size_t n) {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
    vpiHandle assign =
        n < kProcs.size() ? vpi_handle(vpiStmt, kProcs[n]) : nullptr;
    return assign == nullptr ? nullptr : vpi_handle(vpiRepeatControl, assign);
  }

  static vpiHandle ConditionOf(size_t n) {
    vpiHandle repeat = RepeatOf(n);
    vpiHandle control =
        repeat == nullptr ? nullptr : vpi_handle(vpiEventControl, repeat);
    return control == nullptr ? nullptr : vpi_handle(vpiCondition, control);
  }

  static vpiHandle CountOf(size_t n) {
    vpiHandle repeat = RepeatOf(n);
    return repeat == nullptr ? nullptr : vpi_handle(vpiExpr, repeat);
  }

  static void ExpectEdgeOver(vpiHandle edge, int op, const char* signal) {
    EXPECT_EQ(OpOf(edge), op);
    const std::vector<vpiHandle> kSignal = OperandsOf(edge);
    ASSERT_EQ(kSignal.size(), 1U);
    EXPECT_EQ(VpiObjectOf(kSignal[0]), VpiObjectOf(By(signal)));
  }

  static void ExpectEventOr(vpiHandle condition) {
    EXPECT_EQ(OpOf(condition), vpiEventOrOp);
    const std::vector<vpiHandle> kEither = OperandsOf(condition);
    ASSERT_EQ(kEither.size(), 2U);
    EXPECT_EQ(VpiObjectOf(kEither[0]), VpiObjectOf(By("top.c")));
    EXPECT_EQ(VpiObjectOf(kEither[1]), VpiObjectOf(By("top.d")));
  }
};

TEST_F(RepeatControlsEverywhere, ARepeatControlIsItsOwnType) {
  vpiHandle repeat = RepeatOf(0);
  ASSERT_NE(repeat, nullptr);
  EXPECT_EQ(vpi_get(vpiType, repeat), vpiRepeatControl);
  EXPECT_EQ(std::string(vpi_get_str(vpiType, repeat)), "vpiRepeatControl");
}

TEST_F(RepeatControlsEverywhere, ARepeatControlHasNoCondition) {
  vpiHandle repeat = RepeatOf(11);
  ASSERT_NE(repeat, nullptr);
  EXPECT_EQ(vpi_handle(vpiCondition, repeat), nullptr);
}

TEST_F(RepeatControlsEverywhere, APosedgeEventIsAPosedgeOperation) {
  ExpectEdgeOver(ConditionOf(0), vpiPosedgeOp, "top.c");
}

TEST_F(RepeatControlsEverywhere, ANegedgeEventIsANegedgeOperation) {
  ExpectEdgeOver(ConditionOf(1), vpiNegedgeOp, "top.c");
}

TEST_F(RepeatControlsEverywhere, AnEdgeEventIsItsPosedgeOrItsNegedge) {
  vpiHandle condition = ConditionOf(2);
  EXPECT_EQ(OpOf(condition), vpiEventOrOp);
  const std::vector<vpiHandle> kEdges = OperandsOf(condition);
  ASSERT_EQ(kEdges.size(), 2U);
  ExpectEdgeOver(kEdges[0], vpiPosedgeOp, "top.c");
  ExpectEdgeOver(kEdges[1], vpiNegedgeOp, "top.c");
}

TEST_F(RepeatControlsEverywhere, AnOrListIsAnEventOrOperation) {
  ExpectEventOr(ConditionOf(3));
}

TEST_F(RepeatControlsEverywhere, ACommaListIsAnEventOrOperation) {
  ExpectEventOr(ConditionOf(4));
}

TEST_F(RepeatControlsEverywhere, ANamedEventIsTheCondition) {
  vpiHandle condition = ConditionOf(5);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiType, condition), vpiNamedEvent);
  EXPECT_EQ(VpiObjectOf(condition), VpiObjectOf(By("top.e")));
}

TEST_F(RepeatControlsEverywhere, AHierarchicalEventIsTheEventItNames) {
  vpiHandle condition = ConditionOf(6);
  ASSERT_NE(condition, nullptr);
  if (vpi_get(vpiType, condition) == vpiRefObj) {
    condition = vpi_handle(vpiActual, condition);
  }
  EXPECT_EQ(VpiObjectOf(condition), VpiObjectOf(By("top.u.e")));
}

TEST_F(RepeatControlsEverywhere, AnImplicitEventListIsStillAnEventControl) {
  for (size_t n : {size_t{7}, size_t{8}}) {
    vpiHandle repeat = RepeatOf(n);
    ASSERT_NE(repeat, nullptr) << n;
    vpiHandle control = vpi_handle(vpiEventControl, repeat);
    ASSERT_NE(control, nullptr) << n;
    EXPECT_EQ(vpi_get(vpiType, control), vpiEventControl) << n;
    EXPECT_EQ(IntegerOf(vpi_handle(vpiExpr, repeat)), 3) << n;
  }
}

TEST_F(RepeatControlsEverywhere, AnIffGuardIsAnIffOperation) {
  vpiHandle condition = ConditionOf(9);
  EXPECT_EQ(OpOf(condition), vpiIffOp);
  const std::vector<vpiHandle> kGuarded = OperandsOf(condition);
  ASSERT_EQ(kGuarded.size(), 2U);
  EXPECT_EQ(VpiObjectOf(kGuarded[0]), VpiObjectOf(By("top.c")));
  EXPECT_EQ(VpiObjectOf(kGuarded[1]), VpiObjectOf(By("top.en")));
}

TEST_F(RepeatControlsEverywhere, ANonblockingRepeatReachesCountAndEvent) {
  vpiHandle repeat = RepeatOf(10);
  ASSERT_NE(repeat, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, repeat)), VpiObjectOf(By("top.n")));
  ExpectEdgeOver(ConditionOf(10), vpiPosedgeOp, "top.c");
}

TEST_F(RepeatControlsEverywhere, AVariableCountIsTheVariable) {
  EXPECT_EQ(VpiObjectOf(CountOf(11)), VpiObjectOf(By("top.n")));
}

TEST_F(RepeatControlsEverywhere, AParameterCountIsTheParameter) {
  vpiHandle count = CountOf(12);
  ASSERT_NE(count, nullptr);
  EXPECT_EQ(vpi_get(vpiType, count), vpiParameter);
  EXPECT_EQ(VpiObjectOf(count), VpiObjectOf(By("top.P")));
  EXPECT_EQ(IntegerOf(count), 4);
}

TEST_F(RepeatControlsEverywhere, ABitOfALogicVectorCountIsAVarBit) {
  vpiHandle count = CountOf(13);
  ASSERT_NE(count, nullptr);
  EXPECT_EQ(vpi_get(vpiType, count), vpiVarBit);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, count)),
            VpiObjectOf(By("top.v")));
}

TEST_F(RepeatControlsEverywhere, ABitOfAnIntegerCountIsABitSelect) {
  vpiHandle count = CountOf(17);
  ASSERT_NE(count, nullptr);
  EXPECT_EQ(vpi_get(vpiType, count), vpiBitSelect);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, count)),
            VpiObjectOf(By("top.k")));
  EXPECT_EQ(IntegerOf(vpi_handle(vpiIndex, count)), 0);
}

TEST_F(RepeatControlsEverywhere, APartSelectCountIsAPartSelect) {
  vpiHandle count = CountOf(14);
  ASSERT_NE(count, nullptr);
  EXPECT_EQ(vpi_get(vpiType, count), vpiPartSelect);
  EXPECT_EQ(IntegerOf(vpi_handle(vpiLeftRange, count)), 1);
  EXPECT_EQ(IntegerOf(vpi_handle(vpiRightRange, count)), 0);
}

TEST_F(RepeatControlsEverywhere, AnOperationCountIsTheOperation) {
  vpiHandle count = CountOf(15);
  EXPECT_EQ(OpOf(count), vpiAddOp);
  const std::vector<vpiHandle> kTerms = OperandsOf(count);
  ASSERT_EQ(kTerms.size(), 2U);
  EXPECT_EQ(VpiObjectOf(kTerms[0]), VpiObjectOf(By("top.n")));
  EXPECT_EQ(IntegerOf(kTerms[1]), 1);
}

TEST_F(RepeatControlsEverywhere, AFunctionCallCountIsTheCall) {
  vpiHandle count = CountOf(16);
  ASSERT_NE(count, nullptr);
  EXPECT_EQ(vpi_get(vpiType, count), vpiFuncCall);
  EXPECT_EQ(CalleeOf(count), "f");
}

class RepeatControlsInEachPlace : public VpiDesignRun {
 protected:
  static vpiHandle AssignmentIn(vpiHandle stmt) {
    while (stmt != nullptr && vpi_get(vpiType, stmt) != vpiAssignment) {
      const std::vector<vpiHandle> kInner = ObjectsOf(vpiStmt, stmt);
      stmt = kInner.empty() ? nullptr : kInner[0];
    }
    return stmt;
  }

  static vpiHandle RepeatUnder(vpiHandle owner) {
    vpiHandle assign =
        owner == nullptr ? nullptr : AssignmentIn(vpi_handle(vpiStmt, owner));
    return assign == nullptr ? nullptr : vpi_handle(vpiRepeatControl, assign);
  }

  static vpiHandle SoleProcessOf(vpiHandle scope) {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, scope);
    return kProcs.size() == 1 ? kProcs[0] : nullptr;
  }
};

TEST_F(RepeatControlsInEachPlace, ARepeatControlInEachPlaceReachesBoth) {
  Run("package pk; bit c; int v, w; task pt; v = repeat (5) @(c) w; endtask\n"
      "endpackage\n"
      "interface ifc; bit c; int v, w; initial v = repeat (5) @(c) w;\n"
      "endinterface\n"
      "program prg; bit c; int v, w; initial v = repeat (5) @(c) w;\n"
      "endprogram\n"
      "module ma; bit c; int v, w; always v = repeat (5) @(c) w; endmodule\n"
      "module mb; bit c; int v, w;\n"
      "  initial begin begin v = repeat (5) @(c) w; end end\n"
      "endmodule\n"
      "module mc; bit c; int v, w; initial fork v = repeat (5) @(c) w; join\n"
      "endmodule\n"
      "module top; bit c; int v, w; ifc i0(); prg p0(); ma a0(); mb b0();\n"
      "  mc c0();\n"
      "  class C; bit c; int v, w; task ct; v = repeat (5) @(c) w; endtask\n"
      "  endclass\n"
      "  task tk; v = repeat (5) @(c) w; endtask\n"
      "  if (1) begin : g bit c; int v, w; initial v = repeat (5) @(c) w; end\n"
      "  initial #100 $finish;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  const struct {
    const char* where;
    vpiHandle repeat;
  } kPlaces[] = {
      {"pt", RepeatUnder(Named(vpiTask, By("pk"), "pt"))},
      {"i0", RepeatUnder(SoleProcessOf(By("top.i0")))},
      {"p0", RepeatUnder(SoleProcessOf(By("top.p0")))},
      {"a0", RepeatUnder(SoleProcessOf(By("top.a0")))},
      {"b0", RepeatUnder(SoleProcessOf(By("top.b0")))},
      {"c0", RepeatUnder(SoleProcessOf(By("top.c0")))},
      {"ct",
       RepeatUnder(Named(vpiMethods, Named(vpiClassDefn, top, "C"), "ct"))},
      {"tk", RepeatUnder(Named(vpiTask, top, "tk"))},
      {"g", RepeatUnder(SoleProcessOf(By("top.g")))},
  };
  for (const auto& place : kPlaces) {
    ASSERT_NE(place.repeat, nullptr) << place.where;
    EXPECT_EQ(vpi_get(vpiType, place.repeat), vpiRepeatControl) << place.where;
    EXPECT_EQ(IntegerOf(vpi_handle(vpiExpr, place.repeat)), 5) << place.where;
    vpiHandle control = vpi_handle(vpiEventControl, place.repeat);
    ASSERT_NE(control, nullptr) << place.where;
    vpiHandle condition = vpi_handle(vpiCondition, control);
    ASSERT_NE(condition, nullptr) << place.where;
    EXPECT_STREQ(vpi_get_str(vpiName, condition), "c") << place.where;
  }
}

}  // namespace
}  // namespace delta
