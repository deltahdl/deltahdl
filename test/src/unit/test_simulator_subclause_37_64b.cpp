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

class AssignmentsEverywhere : public VpiDesignRun {
 protected:
  static void Walk(vpiHandle stmt, std::vector<vpiHandle>& out, int depth) {
    if (stmt == nullptr || depth > 8) return;
    if (vpi_get(vpiType, stmt) == vpiAssignment) out.push_back(stmt);
    Walk(vpi_handle(vpiStmt, stmt), out, depth + 1);
    Walk(vpi_handle(vpiElseStmt, stmt), out, depth + 1);
    for (vpiHandle inner : ObjectsOf(vpiStmt, stmt)) {
      Walk(inner, out, depth + 1);
    }
  }

  static std::vector<vpiHandle> AssignsUnder(vpiHandle routine) {
    std::vector<vpiHandle> out;
    if (routine != nullptr) Walk(vpi_handle(vpiStmt, routine), out, 0);
    return out;
  }

  static std::vector<vpiHandle> AssignsOfProcesses(vpiHandle scope) {
    std::vector<vpiHandle> out;
    if (scope == nullptr) return out;
    for (vpiHandle proc : ObjectsOf(vpiProcess, scope)) {
      Walk(vpi_handle(vpiStmt, proc), out, 0);
    }
    return out;
  }

  static std::vector<int> PropertyOfEach(int property,
                                         const std::vector<vpiHandle>& objs) {
    std::vector<int> values;
    values.reserve(objs.size());
    for (vpiHandle obj : objs) values.push_back(vpi_get(property, obj));
    return values;
  }

  static std::string FullNameOf(vpiHandle obj) {
    if (obj == nullptr) return "null";
    const char* full = vpi_get_str(vpiFullName, obj);
    return full == nullptr ? "" : full;
  }

  static std::string NameOf(vpiHandle obj) {
    if (obj == nullptr) return "null";
    const char* name = vpi_get_str(vpiName, obj);
    return name == nullptr ? "" : name;
  }
};

TEST_F(AssignmentsEverywhere, EveryAssignmentOperatorReportsItsOperator) {
  Run("module top; int a, b;\n"
      "  initial begin a -= b; a *= b; a /= b; a %= b; a &= b; a |= b;\n"
      "    a ^= b; a <<= b; a >>= b; a >>>= b; end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kAssigns = AssignsOfProcesses(By("top"));
  EXPECT_EQ(PropertyOfEach(vpiOpType, kAssigns),
            (std::vector<int>{vpiSubOp, vpiMultOp, vpiDivOp, vpiModOp,
                              vpiBitAndOp, vpiBitOrOp, vpiBitXorOp, vpiLShiftOp,
                              vpiRShiftOp, vpiArithRShiftOp}));
  for (vpiHandle assign : kAssigns) {
    EXPECT_EQ(vpi_get(vpiBlocking, assign), 1);
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, assign)),
              VpiObjectOf(By("top.a")));
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, assign)),
              VpiObjectOf(By("top.b")));
  }
}

constexpr const char* kTimed =
    "module top; bit c; int a, b, n;\n"
    "  initial begin\n"
    "    a <= #5 b; a = @(c) b; a <= repeat (n) @(c) b;\n"
    "    a = #5 b; a <= @(posedge c) b; a = repeat (3) @(c) b;\n"
    "    a = b; a <= b;\n"
    "  end\n"
    "endmodule\n";

TEST_F(AssignmentsEverywhere, EachTimingControlIsReachedWithEitherOperator) {
  Run(kTimed);
  const std::vector<vpiHandle> kAssigns = AssignsOfProcesses(By("top"));
  ASSERT_EQ(kAssigns.size(), 8U);
  const int kControls[] = {vpiDelayControl, vpiEventControl, vpiRepeatControl};
  for (size_t n = 0; n < 6; ++n) {
    vpiHandle control = vpi_handle(kControls[n % 3], kAssigns[n]);
    ASSERT_NE(control, nullptr) << n;
    EXPECT_EQ(vpi_get(vpiType, control), kControls[n % 3]) << n;
  }
}

TEST_F(AssignmentsEverywhere, AnAssignmentReachesNoControlItDoesNotWrite) {
  Run(kTimed);
  const std::vector<vpiHandle> kAssigns = AssignsOfProcesses(By("top"));
  ASSERT_EQ(kAssigns.size(), 8U);
  const int kControls[] = {vpiDelayControl, vpiEventControl, vpiRepeatControl};
  for (size_t n = 0; n < 8; ++n) {
    for (size_t k = 0; k < 3; ++k) {
      if (n < 6 && n % 3 == k) continue;
      EXPECT_EQ(vpi_handle(kControls[k], kAssigns[n]), nullptr)
          << n << " " << k;
    }
  }
}

TEST_F(AssignmentsEverywhere, ATimingControlLeavesTheBlockingFlagAlone) {
  Run(kTimed);
  EXPECT_EQ(PropertyOfEach(vpiBlocking, AssignsOfProcesses(By("top"))),
            (std::vector<int>{0, 1, 0, 1, 0, 1, 1, 0}));
}

TEST_F(AssignmentsEverywhere, ATimedAssignmentReachesBothSides) {
  Run(kTimed);
  for (vpiHandle assign : AssignsOfProcesses(By("top"))) {
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, assign)),
              VpiObjectOf(By("top.a")));
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, assign)),
              VpiObjectOf(By("top.b")));
  }
}

constexpr const char* kLeftSides =
    "module top; logic [7:0] v; int i; logic [3:0] x, y;\n"
    "  typedef struct { int f; int g; } S; S s;\n"
    "  class C; int p; endclass\n"
    "  C h = new;\n"
    "  initial begin\n"
    "    v[3] = 1; v[7:4] = 2; v[i+:4] = 3; v[i-:4] = 4;\n"
    "    s.f = 5; h.p = 6; {x, y} = 7;\n"
    "  end\n"
    "endmodule\n";

TEST_F(AssignmentsEverywhere, ASelectOnTheLeftIsTheSelectWritten) {
  Run(kLeftSides);
  const std::vector<vpiHandle> kAssigns = AssignsOfProcesses(By("top"));
  ASSERT_EQ(kAssigns.size(), 7U);
  std::vector<int> kinds;
  for (size_t n = 0; n < 4; ++n) {
    vpiHandle lhs = vpi_handle(vpiLhs, kAssigns[n]);
    kinds.push_back(lhs == nullptr ? 0 : vpi_get(vpiType, lhs));
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, lhs)), VpiObjectOf(By("top.v")))
        << n;
  }
  EXPECT_EQ(kinds,
            (std::vector<int>{vpiVarBit, vpiPartSelect, vpiIndexedPartSelect,
                              vpiIndexedPartSelect}));
  EXPECT_EQ(IntegerOf(vpi_handle(vpiIndex, vpi_handle(vpiLhs, kAssigns[0]))),
            3);
  EXPECT_EQ(vpi_get(vpiIndexedPartSelectType, vpi_handle(vpiLhs, kAssigns[2])),
            vpiPosIndexed);
  EXPECT_EQ(vpi_get(vpiIndexedPartSelectType, vpi_handle(vpiLhs, kAssigns[3])),
            vpiNegIndexed);
}

TEST_F(AssignmentsEverywhere, AStructMemberOnTheLeftIsTheMemberWritten) {
  Run(kLeftSides);
  const std::vector<vpiHandle> kAssigns = AssignsOfProcesses(By("top"));
  ASSERT_EQ(kAssigns.size(), 7U);
  vpiHandle member = vpi_handle(vpiLhs, kAssigns[4]);
  ASSERT_NE(member, nullptr);
  EXPECT_EQ(VpiObjectOf(member), VpiObjectOf(By("top.s.f")));
}

TEST_F(AssignmentsEverywhere,
       DISABLED_AClassPropertyOnTheLeftIsThePropertyWritten) {
  Run(kLeftSides);
  const std::vector<vpiHandle> kAssigns = AssignsOfProcesses(By("top"));
  ASSERT_EQ(kAssigns.size(), 7U);
  vpiHandle property = vpi_handle(vpiLhs, kAssigns[5]);
  ASSERT_NE(property, nullptr);
  EXPECT_EQ(NameOf(property), "p");
}

TEST_F(AssignmentsEverywhere, AConcatenationOnTheLeftIsAConcatOperation) {
  Run(kLeftSides);
  const std::vector<vpiHandle> kAssigns = AssignsOfProcesses(By("top"));
  ASSERT_EQ(kAssigns.size(), 7U);
  vpiHandle concat = vpi_handle(vpiLhs, kAssigns[6]);
  ASSERT_NE(concat, nullptr);
  EXPECT_EQ(vpi_get(vpiType, concat), vpiOperation);
  EXPECT_EQ(OpOf(concat), vpiConcatOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(concat);
  ASSERT_EQ(kOperands.size(), 2U);
  EXPECT_EQ(VpiObjectOf(kOperands[0]), VpiObjectOf(By("top.x")));
  EXPECT_EQ(VpiObjectOf(kOperands[1]), VpiObjectOf(By("top.y")));
}

constexpr const char* kPlaces =
    "package pk; int pv, pw;\n"
    "  task pt; pv = pw; pv += 2; endtask\n"
    "  function void pf; pv = pw; pv -= 2; endfunction\n"
    "endpackage\n"
    "interface ifc; int v, w; initial begin v = w; v *= 2; end endinterface\n"
    "program prg; int v, w; initial begin v = w; v /= 2; end endprogram\n"
    "module top; int v, w; ifc i0(); prg p0();\n"
    "  class C; int m, n; task ct; m = n; m |= 2; endtask\n"
    "    function void cf; m = n; m ^= 2; endfunction endclass\n"
    "  task tk; v = w; v &= 2; endtask\n"
    "  function void fn; v = w; v %= 2; endfunction\n"
    "endmodule\n";

struct Place {
  const char* where;
  std::vector<vpiHandle> assigns;
  int compound;
};

class AssignmentsInEachPlace : public AssignmentsEverywhere {
 protected:
  static std::vector<Place> Places() {
    vpiHandle top = By("top");
    vpiHandle cls = Named(vpiClassDefn, top, "C");
    vpiHandle pk = By("pk");
    return {
        {"pt", AssignsUnder(Named(vpiTask, pk, "pt")), vpiAddOp},
        {"pf", AssignsUnder(Named(vpiFunction, pk, "pf")), vpiSubOp},
        {"i0", AssignsOfProcesses(By("top.i0")), vpiMultOp},
        {"p0", AssignsOfProcesses(By("top.p0")), vpiDivOp},
        {"ct", AssignsUnder(Named(vpiMethods, cls, "ct")), vpiBitOrOp},
        {"cf", AssignsUnder(Named(vpiMethods, cls, "cf")), vpiBitXorOp},
        {"tk", AssignsUnder(Named(vpiTask, top, "tk")), vpiBitAndOp},
        {"fn", AssignsUnder(Named(vpiFunction, top, "fn")), vpiModOp},
    };
  }
};

TEST_F(AssignmentsInEachPlace, AnAssignmentInEachPlaceIsAnObject) {
  Run(kPlaces);
  for (const Place& place : Places()) {
    EXPECT_EQ(place.assigns.size(), 2U) << place.where;
  }
}

TEST_F(AssignmentsInEachPlace, AnAssignmentInEachPlaceReportsItsOperator) {
  Run(kPlaces);
  for (const Place& place : Places()) {
    EXPECT_EQ(PropertyOfEach(vpiOpType, place.assigns),
              (std::vector<int>{vpiAssignmentOp, place.compound}))
        << place.where;
    EXPECT_EQ(PropertyOfEach(vpiBlocking, place.assigns),
              (std::vector<int>{1, 1}))
        << place.where;
  }
}

TEST_F(AssignmentsInEachPlace, AnAssignmentInEachPlaceReachesBothSides) {
  Run(kPlaces);
  const char* targets[] = {"pk::pv", "pk::pv", "top.i0.v", "top.p0.v",
                           "",       "",       "top.v",    "top.v"};
  size_t n = 0;
  for (const Place& place : Places()) {
    const char* target = targets[n++];
    ASSERT_FALSE(place.assigns.empty()) << place.where;
    vpiHandle lhs = vpi_handle(vpiLhs, place.assigns[0]);
    vpiHandle rhs = vpi_handle(vpiRhs, place.assigns[0]);
    if (*target == '\0') {
      EXPECT_EQ(NameOf(lhs), "m") << place.where;
      EXPECT_EQ(NameOf(rhs), "n") << place.where;
      continue;
    }
    std::string source(target);
    source.back() = 'w';
    EXPECT_EQ(FullNameOf(lhs), target) << place.where;
    EXPECT_EQ(FullNameOf(rhs), source) << place.where;
  }
}

TEST_F(AssignmentsEverywhere, AnAssignmentInACheckerIsAnObject) {
  Run("checker chk(logic clk); logic v, w;\n"
      "  always_ff @(posedge clk) v <= w;\n"
      "endchecker\n"
      "module top; logic clk; chk k0(clk); endmodule\n");
  const std::vector<vpiHandle> kAssigns = AssignsOfProcesses(By("top.k0"));
  ASSERT_EQ(kAssigns.size(), 1U);
  EXPECT_EQ(vpi_get(vpiBlocking, kAssigns[0]), 0);
  EXPECT_EQ(FullNameOf(vpi_handle(vpiLhs, kAssigns[0])), "top.k0.v");
  EXPECT_EQ(FullNameOf(vpi_handle(vpiRhs, kAssigns[0])), "top.k0.w");
}

TEST_F(AssignmentsEverywhere, AnInterfaceOnTheRightIsTheInterfaceAssigned) {
  Run("interface ifc; logic s; endinterface\n"
      "module top; ifc i0(); virtual ifc vif, vif2;\n"
      "  initial begin vif = i0; vif2 = vif; end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kAssigns = AssignsOfProcesses(By("top"));
  ASSERT_EQ(kAssigns.size(), 2U);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, kAssigns[0])),
            VpiObjectOf(By("top.i0")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, kAssigns[1])),
            VpiObjectOf(By("top.vif")));
}

TEST_F(AssignmentsEverywhere, DISABLED_AUnitVariableIsReachedOnEitherSide) {
  Run("int uk;\n"
      "module top; int x;\n"
      "  initial begin uk = 1; $unit::uk = 2; x = uk; x = $unit::uk; end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kAssigns = AssignsOfProcesses(By("top"));
  ASSERT_EQ(kAssigns.size(), 4U);
  const vpiHandle kSides[] = {
      vpi_handle(vpiLhs, kAssigns[0]), vpi_handle(vpiLhs, kAssigns[1]),
      vpi_handle(vpiRhs, kAssigns[2]), vpi_handle(vpiRhs, kAssigns[3])};
  for (vpiHandle side : kSides) {
    ASSERT_NE(side, nullptr);
    EXPECT_EQ(vpi_get(vpiType, side), vpiIntVar);
    EXPECT_EQ(NameOf(side), "uk");
  }
}

}  // namespace
}  // namespace delta
