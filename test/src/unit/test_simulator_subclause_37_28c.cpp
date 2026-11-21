#include <gtest/gtest.h>

#include <string>
#include <tuple>
#include <vector>

#include "fixture_vpi_parameters.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ParameterValuesOfARun : public ParametersOfEveryPlace {
 protected:
  static void ExpectOneAssign(const char* instance, int value, int by_name) {
    SCOPED_TRACE(instance);
    const std::vector<vpiHandle> kAssigns =
        ObjectsOf(vpiParamAssign, By(instance));
    ASSERT_EQ(kAssigns.size(), 1U);
    EXPECT_EQ(Str(vpiName, Through(vpiLhs, kAssigns[0])), "W");
    EXPECT_EQ(KindOf(Through(vpiLhs, kAssigns[0])), vpiParameter);
    EXPECT_EQ(ValueOf(Through(vpiRhs, kAssigns[0])), value);
    EXPECT_EQ(Flag(vpiConnByName, kAssigns[0]), by_name);
  }

  static void ExpectIterationsGenvar(vpiHandle op) {
    const std::vector<vpiHandle> kOperands = OperandsOf(op);
    ASSERT_EQ(kOperands.size(), 2U);
    vpiHandle ref = kOperands[0];
    EXPECT_EQ(KindOf(ref), vpiParameter);
    EXPECT_EQ(Flag(vpiLocalParam, ref), 1);
    EXPECT_EQ(Str(vpiName, ref), "i");
    EXPECT_EQ(ValueOf(ref), 1);
  }
};

constexpr const char* kOverrides =
    "package pkg;\n"
    "  parameter int P = 5;\n"
    "endpackage\n"
    "interface ifc #(parameter int W = 1) (); endinterface\n"
    "program prg #(parameter int W = 1) (); endprogram\n"
    "module m #(parameter int W = 2, parameter type T = int) (); endmodule\n"
    "module n #(parameter int N, parameter type U) (); endmodule\n"
    "module top;\n"
    "  parameter int P = 5;\n"
    "  parameter logic [7:0] R = 8'h3c;\n"
    "  parameter [3:0] X = 5;\n"
    "  parameter signed [3:0] SX = -2;\n"
    "  parameter Q = 9;\n"
    "  m #(.W(4)) u();\n"
    "  m #(6) v();\n"
    "  m #(.T(byte)) w();\n"
    "  m x();\n"
    "  defparam x.W = 8;\n"
    "  n #(3, logic [2:0]) z();\n"
    "  ifc #(.W(7)) i0();\n"
    "  ifc #(9) i1();\n"
    "  prg #(.W(4)) p0();\n"
    "  prg #(5) p1();\n"
    "endmodule\n";

TEST_F(ParameterValuesOfARun, APackagesParameterIsReadAsItsValue) {
  Run(kOverrides);
  EXPECT_EQ(ValueOf(ParameterAt("pkg", "P")), 5);
}

TEST_F(ParameterValuesOfARun, AnOverriddenParameterIsReadAsItsOverride) {
  Run(kOverrides);
  EXPECT_EQ(ValueOf(ParameterAt("top.u", "W")), 4);
  EXPECT_EQ(ValueOf(ParameterAt("top.v", "W")), 6);
  EXPECT_EQ(ValueOf(ParameterAt("top.w", "W")), 2);
  EXPECT_EQ(ValueOf(ParameterAt("top.x", "W")), 8);
  EXPECT_EQ(ValueOf(ParameterAt("top.z", "N")), 3);
}

TEST_F(ParameterValuesOfARun, AnInterfacesOrProgramsOverriddenParameterIsRead) {
  Run(kOverrides);
  EXPECT_EQ(ValueOf(ParameterAt("top.i0", "W")), 7);
  EXPECT_EQ(ValueOf(ParameterAt("top.i1", "W")), 9);
  EXPECT_EQ(ValueOf(ParameterAt("top.p0", "W")), 4);
  EXPECT_EQ(ValueOf(ParameterAt("top.p1", "W")), 5);
}

TEST_F(ParameterValuesOfARun, AnOverriddenTypeParametersExprIsStillItsDefault) {
  Run(kOverrides);
  vpiHandle type = ParameterAt("top.w", "T");
  ASSERT_NE(type, nullptr);
  EXPECT_EQ(KindOf(Through(vpiTypespec, type)), vpiByteTypespec);
  EXPECT_EQ(KindOf(Through(vpiExpr, type)), vpiIntTypespec);
}

TEST_F(ParameterValuesOfARun, AParameterPortWithNoDefaultHasNoExpr) {
  Run(kOverrides);
  vpiHandle value = ParameterAt("top.z", "N");
  vpiHandle type = ParameterAt("top.z", "U");
  ASSERT_NE(value, nullptr);
  ASSERT_NE(type, nullptr);
  EXPECT_EQ(Through(vpiExpr, value), nullptr);
  EXPECT_EQ(Through(vpiExpr, type), nullptr);
  EXPECT_EQ(ValueOf(value), 3);
  EXPECT_EQ(KindOf(Through(vpiTypespec, type)), vpiLogicTypespec);
}

TEST_F(ParameterValuesOfARun,
       DISABLED_AnInstanceOverridingATypeParameterHoldsItsAssign) {
  Run(kOverrides);
  const std::vector<vpiHandle> kAssigns =
      ObjectsOf(vpiParamAssign, By("top.w"));
  ASSERT_EQ(kAssigns.size(), 1U);
  vpiHandle lhs = Through(vpiLhs, kAssigns[0]);
  EXPECT_EQ(KindOf(lhs), vpiTypeParameter);
  EXPECT_EQ(Str(vpiName, lhs), "T");
  EXPECT_EQ(KindOf(Through(vpiRhs, kAssigns[0])), vpiByteTypespec);
  EXPECT_EQ(Flag(vpiConnByName, kAssigns[0]), 1);
}

TEST_F(ParameterValuesOfARun,
       DISABLED_AnInstanceOverridingByPositionHoldsAnAssignPerValue) {
  Run(kOverrides);
  const std::vector<vpiHandle> kAssigns =
      ObjectsOf(vpiParamAssign, By("top.z"));
  ASSERT_EQ(kAssigns.size(), 2U);
  EXPECT_EQ(Str(vpiName, Through(vpiLhs, kAssigns[0])), "N");
  EXPECT_EQ(ValueOf(Through(vpiRhs, kAssigns[0])), 3);
  EXPECT_EQ(Str(vpiName, Through(vpiLhs, kAssigns[1])), "U");
  EXPECT_EQ(KindOf(Through(vpiRhs, kAssigns[1])), vpiLogicTypespec);
  for (vpiHandle assign : kAssigns) EXPECT_EQ(Flag(vpiConnByName, assign), 0);
}

TEST_F(ParameterValuesOfARun,
       AnInterfaceOrProgramInstanceHoldsItsParamAssigns) {
  Run(kOverrides);
  ExpectOneAssign("top.i0", 7, 1);
  ExpectOneAssign("top.i1", 9, 0);
  ExpectOneAssign("top.p0", 4, 1);
  ExpectOneAssign("top.p1", 5, 0);
}

TEST_F(ParameterValuesOfARun, AParamAssignReachesTheModuleOfItsInstance) {
  Run(kOverrides);
  for (const auto& [holder, module] :
       {std::tuple{"top.u", "top.u"}, std::tuple{"top.v", "top.v"},
        std::tuple{"top.i0", "top"}, std::tuple{"top.p1", "top"}}) {
    SCOPED_TRACE(holder);
    const std::vector<vpiHandle> kAssigns =
        ObjectsOf(vpiParamAssign, By(holder));
    ASSERT_EQ(kAssigns.size(), 1U);
    EXPECT_EQ(Reached(vpiModule, kAssigns[0]), VpiObjectOf(By(module)));
  }
}

TEST_F(ParameterValuesOfARun,
       DISABLED_AParamAssignReachesTheInstanceHoldingItAsScope) {
  Run(kOverrides);
  for (const char* holder : {"top.u", "top.z", "top.i0", "top.p1"}) {
    SCOPED_TRACE(holder);
    const std::vector<vpiHandle> kAssigns =
        ObjectsOf(vpiParamAssign, By(holder));
    ASSERT_FALSE(kAssigns.empty());
    for (vpiHandle assign : kAssigns) {
      EXPECT_EQ(Reached(vpiScope, assign), VpiObjectOf(By(holder)));
    }
  }
}

TEST_F(ParameterValuesOfARun, AValueParameterReportsItsSize) {
  Run(kOverrides);
  for (const auto& [name, size] : {std::tuple{"P", 32}, std::tuple{"R", 8},
                                   std::tuple{"X", 4}, std::tuple{"SX", 4}}) {
    SCOPED_TRACE(name);
    EXPECT_EQ(Flag(vpiSize, ParameterAt("top", name)), size);
  }
}

TEST_F(ParameterValuesOfARun, DISABLED_AValueParameterReportsItsSign) {
  Run(kOverrides);
  for (const auto& [name, is_signed] :
       {std::tuple{"P", 1}, std::tuple{"SX", 1}, std::tuple{"R", 0},
        std::tuple{"X", 0}}) {
    SCOPED_TRACE(name);
    EXPECT_EQ(Flag(vpiSigned, ParameterAt("top", name)), is_signed);
  }
}

TEST_F(ParameterValuesOfARun, AnUntypedParametersRangeGivesItsBounds) {
  Run(kOverrides);
  vpiHandle x = ParameterAt("top", "X");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(ValueOf(Through(vpiLeftRange, x)), 3);
  EXPECT_EQ(ValueOf(Through(vpiRightRange, x)), 0);
  EXPECT_EQ(ValueOf(x), 5);
}

TEST_F(ParameterValuesOfARun, AParameterWithNoRangeGivesNoBounds) {
  Run(kOverrides);
  for (const char* name : {"P", "Q"}) {
    SCOPED_TRACE(name);
    vpiHandle param = ParameterAt("top", name);
    ASSERT_NE(param, nullptr);
    EXPECT_EQ(Through(vpiLeftRange, param), nullptr);
    EXPECT_EQ(Through(vpiRightRange, param), nullptr);
  }
}

constexpr const char* kTypeAliases =
    "module top;\n"
    "  typedef enum {A, B} e_t;\n"
    "  typedef e_t a_t;\n"
    "  parameter type AT = a_t;\n"
    "  class K #(type T = e_t);\n"
    "    localparam type L = e_t;\n"
    "  endclass\n"
    "  class J #(type T = int);\n"
    "    localparam type L = T;\n"
    "  endclass\n"
    "  J #(a_t) j = new;\n"
    "endmodule\n";

TEST_F(ParameterValuesOfARun, ATypeParameterKeepsAnAliasOfAnAlias) {
  Run(kTypeAliases);
  vpiHandle typespec = Through(vpiTypespec, ParameterAt("top", "AT"));
  EXPECT_EQ(KindOf(typespec), vpiEnumTypespec);
  EXPECT_EQ(Str(vpiName, typespec), "a_t");
}

TEST_F(ParameterValuesOfARun,
       DISABLED_AClassesTypeParametersTypespecIsTheTypeItNames) {
  Run(kTypeAliases);
  vpiHandle defn = Named(vpiClassDefn, By("top"), "K");
  ASSERT_NE(defn, nullptr);
  for (const char* name : {"T", "L"}) {
    SCOPED_TRACE(name);
    EXPECT_EQ(Str(vpiName, Through(vpiTypespec, ParameterIn(defn, name))),
              "e_t");
  }
  vpiHandle plain = ParameterIn(Named(vpiClassDefn, By("top"), "J"), "T");
  EXPECT_EQ(KindOf(Through(vpiTypespec, plain)), vpiIntTypespec);
}

TEST_F(ParameterValuesOfARun,
       DISABLED_ASpecializationsTypeParameterIsTheTypedefItNames) {
  Run(kTypeAliases);
  vpiHandle obj = Through(vpiClassObj, By("top.j"));
  ASSERT_NE(obj, nullptr);
  for (const char* name : {"T", "L"}) {
    SCOPED_TRACE(name);
    EXPECT_EQ(Str(vpiName, Through(vpiTypespec, ParameterIn(obj, name))),
              "a_t");
  }
}

constexpr const char* kClassBodies =
    "module top;\n"
    "  class D #(int N = 2);\n"
    "    parameter int B = N * 2;\n"
    "    localparam type BT = byte;\n"
    "  endclass\n"
    "  class E;\n"
    "    parameter int B = 3;\n"
    "  endclass\n"
    "  D #(5) d = new;\n"
    "  D #(7) d2 = new;\n"
    "  E e = new;\n"
    "endmodule\n";

TEST_F(ParameterValuesOfARun, AClassObjsBodyParameterIsLocal) {
  Run(kClassBodies);
  for (const char* var : {"top.d", "top.e"}) {
    SCOPED_TRACE(var);
    vpiHandle body = ParameterIn(Through(vpiClassObj, By(var)), "B");
    ASSERT_NE(body, nullptr);
    EXPECT_EQ(Flag(vpiLocalParam, body), 1);
  }
  EXPECT_EQ(
      Flag(vpiLocalParam, ParameterIn(Through(vpiClassObj, By("top.d")), "N")),
      0);
}

TEST_F(ParameterValuesOfARun, DISABLED_AClassObjYieldsItsBodyTypeParameter) {
  Run(kClassBodies);
  vpiHandle obj = Through(vpiClassObj, By("top.d"));
  ASSERT_NE(obj, nullptr);
  EXPECT_EQ(NamesOf(vpiParameter, obj),
            (std::vector<std::string>{"B", "BT", "N"}));
  vpiHandle type = ParameterIn(obj, "BT");
  EXPECT_EQ(KindOf(type), vpiTypeParameter);
  EXPECT_EQ(Flag(vpiLocalParam, type), 1);
}

TEST_F(ParameterValuesOfARun, AClassObjsParametersMatchItsClassTypespec) {
  Run(kClassBodies);
  for (const auto& [var, n, b] :
       {std::tuple{"top.d", 5, 10}, std::tuple{"top.d2", 7, 14},
        std::tuple{"top.e", -1, 3}}) {
    SCOPED_TRACE(var);
    vpiHandle obj = Through(vpiClassObj, By(var));
    ASSERT_NE(obj, nullptr);
    vpiHandle typespec = Through(vpiClassTypespec, obj);
    ASSERT_NE(typespec, nullptr);
    EXPECT_EQ(ValueOf(ParameterIn(obj, "N")), n);
    EXPECT_EQ(ValueOf(ParameterIn(typespec, "N")), n);
    EXPECT_EQ(ValueOf(ParameterIn(obj, "B")), b);
    EXPECT_EQ(ValueOf(ParameterIn(typespec, "B")), b);
  }
}

constexpr const char* kGenvarUses =
    "module top;\n"
    "  for (genvar i = 0; i < 2; i++) begin : g\n"
    "    int x;\n"
    "    initial x = i + 5;\n"
    "    if (1) begin : h\n"
    "      wire [31:0] w;\n"
    "      assign w = i + 7;\n"
    "    end\n"
    "    localparam int P = i + 1;\n"
    "    wire [i:0] d;\n"
    "  end\n"
    "endmodule\n";

TEST_F(ParameterValuesOfARun,
       DISABLED_AGenvarInAProceduralStatementIsALocalParameter) {
  Run(kGenvarUses);
  const std::vector<vpiHandle> kProcesses =
      ObjectsOf(vpiProcess, By("top.g[1]"));
  ASSERT_EQ(kProcesses.size(), 1U);
  ExpectIterationsGenvar(Through(vpiRhs, Through(vpiStmt, kProcesses[0])));
}

TEST_F(ParameterValuesOfARun,
       AGenvarInANestedGenScopeIsTheIterationsParameter) {
  Run(kGenvarUses);
  const std::vector<vpiHandle> kAssigns =
      ObjectsOf(vpiContAssign, By("top.g[1].h"));
  ASSERT_EQ(kAssigns.size(), 1U);
  ExpectIterationsGenvar(Through(vpiRhs, kAssigns[0]));
}

TEST_F(ParameterValuesOfARun, AGenvarInADeclarationGivesTheIterationsValue) {
  Run(kGenvarUses);
  EXPECT_EQ(ValueOf(ParameterAt("top.g[0]", "P")), 1);
  EXPECT_EQ(ValueOf(ParameterAt("top.g[1]", "P")), 2);
  EXPECT_EQ(Flag(vpiSize, By("top.g[0].d")), 1);
  EXPECT_EQ(Flag(vpiSize, By("top.g[1].d")), 2);
}

TEST_F(ParameterValuesOfARun,
       DISABLED_AGenvarInALocalparamsExprIsALocalParameter) {
  Run(kGenvarUses);
  ExpectIterationsGenvar(Through(vpiExpr, ParameterAt("top.g[1]", "P")));
}

TEST_F(ParameterValuesOfARun, DISABLED_AGenvarInANetsRangeGivesItsBound) {
  Run(kGenvarUses);
  EXPECT_EQ(ValueOf(Through(vpiLeftRange, By("top.g[0].d"))), 0);
  EXPECT_EQ(ValueOf(Through(vpiLeftRange, By("top.g[1].d"))), 1);
  EXPECT_EQ(ValueOf(Through(vpiRightRange, By("top.g[1].d"))), 0);
}

}  // namespace
}  // namespace delta
