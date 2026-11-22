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
    "module top; bit clk, c, a; int x, y; sub u();\n"
    "  sequence s(v); @(posedge clk) v; endsequence\n"
    "  class K; event e; endclass\n"
    "  K obj = new;\n"
    "  initial @(*) x = y;\n"
    "  initial @(negedge clk) x = 1;\n"
    "  initial @(c) x = 2;\n"
    "  initial @(s(a)) x = 3;\n"
    "  initial x = @(posedge c) y;\n"
    "  initial x = repeat (3) @(c) y;\n"
    "  initial @(c) begin x = 4; y = 5; end\n"
    "  initial @(c) if (a) x = 6;\n"
    "  initial @(c) @(clk) x = 7;\n"
    "  initial @(top.u.e) x = 8;\n"
    "  initial @(obj.e) x = 9;\n"
    "endmodule\n";

class EventControlsEverywhere : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run(kForms);
  }

  static vpiHandle BodyOf(size_t n) {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
    return n < kProcs.size() ? vpi_handle(vpiStmt, kProcs[n]) : nullptr;
  }

  static vpiHandle ConditionOf(size_t n) {
    vpiHandle control = BodyOf(n);
    return control == nullptr ? nullptr : vpi_handle(vpiCondition, control);
  }

  static vpiHandle EventReachedBy(vpiHandle condition) {
    if (condition == nullptr) return nullptr;
    if (vpi_get(vpiType, condition) == vpiRefObj) {
      return vpi_handle(vpiActual, condition);
    }
    return condition;
  }
};

TEST_F(EventControlsEverywhere, AParenthesizedImplicitListWritesNoCondition) {
  vpiHandle control = BodyOf(0);
  ASSERT_NE(control, nullptr);
  EXPECT_EQ(vpi_get(vpiType, control), vpiEventControl);
  EXPECT_EQ(vpi_handle(vpiCondition, control), nullptr);
  vpiHandle guarded = vpi_handle(vpiStmt, control);
  ASSERT_NE(guarded, nullptr);
  EXPECT_EQ(vpi_get(vpiType, guarded), vpiAssignment);
}

TEST_F(EventControlsEverywhere, ANegedgeEventIsANegedgeOperation) {
  vpiHandle condition = ConditionOf(1);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiType, condition), vpiOperation);
  EXPECT_EQ(OpOf(condition), vpiNegedgeOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(condition);
  ASSERT_EQ(kOperands.size(), 1U);
  EXPECT_EQ(VpiObjectOf(kOperands[0]), VpiObjectOf(By("top.clk")));
}

TEST_F(EventControlsEverywhere, AVariableEventIsTheConditionItself) {
  EXPECT_EQ(VpiObjectOf(ConditionOf(2)), VpiObjectOf(By("top.c")));
}

TEST_F(EventControlsEverywhere, ASequenceEventWithArgumentsCarriesThem) {
  vpiHandle condition = ConditionOf(3);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiType, condition), vpiSequenceInst);
  vpiHandle decl = vpi_handle(vpiSequenceDecl, condition);
  ASSERT_NE(decl, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, decl), "top.s");
  const std::vector<vpiHandle> kArguments = ObjectsOf(vpiArgument, condition);
  ASSERT_EQ(kArguments.size(), 1U);
  EXPECT_EQ(VpiObjectOf(kArguments[0]), VpiObjectOf(By("top.a")));
}

TEST_F(EventControlsEverywhere, ABlockingAssignmentsEventControlHasNoStmt) {
  vpiHandle assign = BodyOf(4);
  ASSERT_NE(assign, nullptr);
  EXPECT_EQ(vpi_get(vpiBlocking, assign), 1);
  vpiHandle control = vpi_handle(vpiEventControl, assign);
  ASSERT_NE(control, nullptr);
  EXPECT_EQ(vpi_get(vpiType, control), vpiEventControl);
  EXPECT_EQ(vpi_handle(vpiStmt, control), nullptr);
  EXPECT_EQ(OpOf(vpi_handle(vpiCondition, control)), vpiPosedgeOp);
}

TEST_F(EventControlsEverywhere, ARepeatedEventControlHasNoStmt) {
  vpiHandle assign = BodyOf(5);
  ASSERT_NE(assign, nullptr);
  vpiHandle control =
      vpi_handle(vpiEventControl, vpi_handle(vpiRepeatControl, assign));
  ASSERT_NE(control, nullptr);
  EXPECT_EQ(vpi_get(vpiType, control), vpiEventControl);
  EXPECT_EQ(vpi_handle(vpiStmt, control), nullptr);
}

TEST_F(EventControlsEverywhere, AGuardedBlockIsTheStmt) {
  vpiHandle guarded = vpi_handle(vpiStmt, BodyOf(6));
  ASSERT_NE(guarded, nullptr);
  EXPECT_EQ(vpi_get(vpiType, guarded), vpiBegin);
  EXPECT_EQ(KindsOf(vpiStmt, guarded),
            (std::vector<int>{vpiAssignment, vpiAssignment}));
}

TEST_F(EventControlsEverywhere, AGuardedIfIsTheStmt) {
  vpiHandle guarded = vpi_handle(vpiStmt, BodyOf(7));
  ASSERT_NE(guarded, nullptr);
  EXPECT_EQ(vpi_get(vpiType, guarded), vpiIf);
}

TEST_F(EventControlsEverywhere, AGuardedEventControlIsTheStmt) {
  vpiHandle inner = vpi_handle(vpiStmt, BodyOf(8));
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(vpi_get(vpiType, inner), vpiEventControl);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, inner)),
            VpiObjectOf(By("top.clk")));
  vpiHandle guarded = vpi_handle(vpiStmt, inner);
  ASSERT_NE(guarded, nullptr);
  EXPECT_EQ(vpi_get(vpiType, guarded), vpiAssignment);
}

TEST_F(EventControlsEverywhere, AHierarchicalEventIsReached) {
  EXPECT_EQ(VpiObjectOf(EventReachedBy(ConditionOf(9))),
            VpiObjectOf(By("top.u.e")));
}

TEST_F(EventControlsEverywhere, DISABLED_AClassMembersEventIsReached) {
  vpiHandle event = EventReachedBy(ConditionOf(10));
  ASSERT_NE(event, nullptr);
  EXPECT_EQ(vpi_get(vpiType, event), vpiNamedEvent);
  EXPECT_STREQ(vpi_get_str(vpiName, event), "e");
}

class EventControlsInEachPlace : public VpiDesignRun {
 protected:
  static vpiHandle ControlOf(vpiHandle body) {
    if (body == nullptr) return nullptr;
    if (vpi_get(vpiType, body) == vpiEventControl) return body;
    const std::vector<vpiHandle> kInner = ObjectsOf(vpiStmt, body);
    return kInner.size() == 1 ? ControlOf(kInner[0]) : nullptr;
  }

  static vpiHandle ProcessControl(const char* scope) {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By(scope));
    return kProcs.size() == 1 ? ControlOf(vpi_handle(vpiStmt, kProcs[0]))
                              : nullptr;
  }

  static vpiHandle RoutineControl(vpiHandle routine) {
    return routine == nullptr ? nullptr
                              : ControlOf(vpi_handle(vpiStmt, routine));
  }
};

TEST_F(EventControlsInEachPlace, AnEventControlInEachPlaceGuardsItsStmt) {
  Run("package pk; bit pc; int pv; task pt; @(pc) pv = 1; endtask\n"
      "endpackage\n"
      "interface ifc; bit c; int v; initial @(c) v = 1; endinterface\n"
      "program prg; bit c; int v; initial @(c) v = 1; endprogram\n"
      "checker chk(logic clk); logic v;\n"
      "  always_ff @(posedge clk) v <= 1;\n"
      "endchecker\n"
      "module top; bit c; int v; ifc i0(); prg p0(); chk k0(c);\n"
      "  class C; bit cc; int m; task ct; @(cc) m = 1; endtask endclass\n"
      "  task tk; @(c) v = 1; endtask\n"
      "endmodule\n");
  vpiHandle top = By("top");
  const struct {
    const char* where;
    vpiHandle control;
  } kPlaces[] = {
      {"pt", RoutineControl(Named(vpiTask, By("pk"), "pt"))},
      {"i0", ProcessControl("top.i0")},
      {"p0", ProcessControl("top.p0")},
      {"k0", ProcessControl("top.k0")},
      {"ct",
       RoutineControl(Named(vpiMethods, Named(vpiClassDefn, top, "C"), "ct"))},
      {"tk", RoutineControl(Named(vpiTask, top, "tk"))},
  };
  for (const auto& place : kPlaces) {
    ASSERT_NE(place.control, nullptr) << place.where;
    EXPECT_EQ(vpi_get(vpiType, place.control), vpiEventControl) << place.where;
    EXPECT_NE(vpi_handle(vpiCondition, place.control), nullptr) << place.where;
    vpiHandle guarded = vpi_handle(vpiStmt, place.control);
    ASSERT_NE(guarded, nullptr) << place.where;
    EXPECT_EQ(vpi_get(vpiType, guarded), vpiAssignment) << place.where;
  }
}

}  // namespace
}  // namespace delta
