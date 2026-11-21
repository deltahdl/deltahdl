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

class ParameterPlacesOfARun : public ParametersOfEveryPlace {};

constexpr const char* kPlaces =
    "parameter int UP = 11;\n"
    "parameter type UT = int;\n"
    "package pkg;\n"
    "  parameter int PP = 3;\n"
    "  parameter type PT = byte;\n"
    "endpackage\n"
    "interface ifc #(parameter int W = 1) ();\n"
    "  parameter int IP = 2;\n"
    "  if (1) begin : g\n"
    "    parameter int GP = 5;\n"
    "  end\n"
    "endinterface\n"
    "program prg #(parameter int W = 1) ();\n"
    "  parameter int QP = 3;\n"
    "  if (1) begin : g\n"
    "    parameter int GP = 6;\n"
    "  end\n"
    "endprogram\n"
    "interface bare_ifc;\n"
    "  parameter int BI = 1;\n"
    "endinterface\n"
    "program bare_prg;\n"
    "  parameter int BQ = 1;\n"
    "endprogram\n"
    "module m #(parameter int W = 2, parameter type T = int,\n"
    "           localparam int ML = 4) ();\n"
    "  parameter int MB = 3;\n"
    "endmodule\n"
    "module top;\n"
    "  parameter int P = 5;\n"
    "  parameter type T = shortint;\n"
    "  localparam type LT = byte;\n"
    "  m u();\n"
    "  ifc i0();\n"
    "  prg p0();\n"
    "  bare_ifc b0();\n"
    "  bare_prg b1();\n"
    "  if (1) begin : g\n"
    "    parameter int GP = 1;\n"
    "    parameter type GT = bit;\n"
    "  end\n"
    "  case (2)\n"
    "    1: begin : c1 parameter int CP = 1; end\n"
    "    2: begin : c2 parameter int CP = 2; end\n"
    "  endcase\n"
    "  class C #(int N = 1, type CT = int);\n"
    "    parameter int BP = 4;\n"
    "    localparam type BT = byte;\n"
    "  endclass\n"
    "  task t; parameter int TP = 3; endtask\n"
    "  function int f; parameter int FP = 4; return FP; endfunction\n"
    "  initial begin : nb parameter int NP = 5; end\n"
    "  initial fork : nf parameter int KP = 6; join\n"
    "endmodule\n";

TEST_F(ParameterPlacesOfARun, AParameterReachesTheModuleItIsInside) {
  Run(kPlaces);
  for (const auto& [scope, name, module] :
       {std::tuple{"top", "P", "top"}, std::tuple{"top", "T", "top"},
        std::tuple{"top", "LT", "top"}, std::tuple{"top.u", "W", "top.u"},
        std::tuple{"top.u", "T", "top.u"}, std::tuple{"top.u", "MB", "top.u"},
        std::tuple{"top.i0", "IP", "top"}, std::tuple{"top.p0", "QP", "top"},
        std::tuple{"top.g", "GT", "top"}, std::tuple{"top.c2", "CP", "top"},
        std::tuple{"top.i0.g", "GP", "top"}}) {
    SCOPED_TRACE(std::string(scope) + "." + name);
    vpiHandle param = ParameterAt(scope, name);
    ASSERT_NE(param, nullptr);
    EXPECT_EQ(Reached(vpiModule, param), VpiObjectOf(By(module)));
  }
  for (const char* name : {"PP", "PT"}) {
    vpiHandle param = ParameterAt("pkg", name);
    ASSERT_NE(param, nullptr) << name;
    EXPECT_EQ(Through(vpiModule, param), nullptr) << name;
  }
}

TEST_F(ParameterPlacesOfARun, DISABLED_AParameterReachesTheScopeDeclaringIt) {
  Run(kPlaces);
  for (const auto& [scope, name] :
       {std::tuple{"top", "P"}, std::tuple{"top", "T"}, std::tuple{"top", "LT"},
        std::tuple{"top.u", "W"}, std::tuple{"top.u", "T"},
        std::tuple{"top.u", "ML"}, std::tuple{"pkg", "PP"},
        std::tuple{"pkg", "PT"}, std::tuple{"top.i0", "IP"},
        std::tuple{"top.p0", "QP"}, std::tuple{"top.g", "GP"},
        std::tuple{"top.g", "GT"}, std::tuple{"top.c2", "CP"},
        std::tuple{"top.i0.g", "GP"}, std::tuple{"top.p0.g", "GP"}}) {
    SCOPED_TRACE(std::string(scope) + "." + name);
    vpiHandle param = ParameterAt(scope, name);
    ASSERT_NE(param, nullptr);
    EXPECT_EQ(Reached(vpiScope, param), VpiObjectOf(By(scope)));
  }
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(defn, nullptr);
  for (const char* name : {"N", "CT", "BP", "BT"}) {
    SCOPED_TRACE(name);
    vpiHandle param = ParameterIn(defn, name);
    ASSERT_NE(param, nullptr);
    EXPECT_EQ(Reached(vpiScope, param), VpiObjectOf(defn));
  }
}

TEST_F(ParameterPlacesOfARun,
       DISABLED_ASubroutinesOrBlocksParameterReachesItAsScope) {
  Run(kPlaces);
  for (const auto& [full, scope] :
       {std::tuple{"top.t.TP", Named(vpiTaskFunc, By("top"), "t")},
        std::tuple{"top.f.FP", Named(vpiTaskFunc, By("top"), "f")},
        std::tuple{"top.nb.NP", By("top.nb")},
        std::tuple{"top.nf.KP", By("top.nf")}}) {
    SCOPED_TRACE(full);
    vpiHandle param = By(full);
    ASSERT_NE(param, nullptr);
    EXPECT_EQ(Str(vpiFullName, param), full);
    EXPECT_EQ(Reached(vpiScope, param), VpiObjectOf(scope));
    EXPECT_EQ(Reached(vpiModule, param), VpiObjectOf(By("top")));
  }
}

TEST_F(ParameterPlacesOfARun, DISABLED_TheUnitsParametersAreItsOwn) {
  Run(kPlaces);
  vpiHandle unit = UnitScope();
  ASSERT_NE(unit, nullptr);
  EXPECT_EQ(NamesOf(vpiParameter, unit),
            (std::vector<std::string>{"UP", "UT"}));
  vpiHandle value = ParameterIn(unit, "UP");
  vpiHandle type = ParameterIn(unit, "UT");
  EXPECT_EQ(KindOf(value), vpiParameter);
  EXPECT_EQ(KindOf(type), vpiTypeParameter);
  EXPECT_EQ(ValueOf(value), 11);
  EXPECT_EQ(Str(vpiFullName, value), "$unit::UP");
  for (vpiHandle param : {value, type}) {
    EXPECT_EQ(Flag(vpiLocalParam, param), 1);
    EXPECT_EQ(Reached(vpiScope, param), VpiObjectOf(unit));
    EXPECT_EQ(Through(vpiModule, param), nullptr);
  }
}

TEST_F(ParameterPlacesOfARun, AParametersFullNameFollowsItsScope) {
  Run(kPlaces);
  EXPECT_EQ(Str(vpiFullName, ParameterAt("top", "P")), "top.P");
  EXPECT_EQ(Str(vpiFullName, ParameterAt("top", "T")), "top.T");
  EXPECT_EQ(Str(vpiFullName, ParameterAt("top.u", "W")), "top.u.W");
  EXPECT_EQ(Str(vpiFullName, ParameterAt("top.u", "T")), "top.u.T");
  EXPECT_EQ(Str(vpiFullName, ParameterAt("top.i0", "IP")), "top.i0.IP");
  EXPECT_EQ(Str(vpiFullName, ParameterAt("top.g", "GT")), "top.g.GT");
  EXPECT_EQ(Str(vpiFullName, ParameterAt("top.c2", "CP")), "top.c2.CP");
}

TEST_F(ParameterPlacesOfARun,
       AModulesLocalparamTypeIsLocalAndParameterTypeIsNot) {
  Run(kPlaces);
  EXPECT_EQ(KindOf(ParameterAt("top", "LT")), vpiTypeParameter);
  EXPECT_EQ(Flag(vpiLocalParam, ParameterAt("top", "LT")), 1);
  EXPECT_EQ(Flag(vpiLocalParam, ParameterAt("top", "T")), 0);
}

TEST_F(ParameterPlacesOfARun, ABodyParameterBesideAParameterPortListIsLocal) {
  Run(kPlaces);
  EXPECT_EQ(Flag(vpiLocalParam, ParameterAt("top.u", "MB")), 1);
  EXPECT_EQ(Flag(vpiLocalParam, ParameterAt("top.i0", "IP")), 1);
  EXPECT_EQ(Flag(vpiLocalParam, ParameterAt("top.p0", "QP")), 1);
  EXPECT_EQ(Flag(vpiLocalParam, ParameterAt("top.u", "W")), 0);
  EXPECT_EQ(Flag(vpiLocalParam, ParameterAt("top.u", "T")), 0);
}

TEST_F(ParameterPlacesOfARun, ALocalparamInAParameterPortListIsLocal) {
  Run(kPlaces);
  EXPECT_EQ(Flag(vpiLocalParam, ParameterAt("top.u", "ML")), 1);
}

TEST_F(ParameterPlacesOfARun,
       ABodyParameterWithoutAParameterPortListIsNotLocal) {
  Run(kPlaces);
  EXPECT_EQ(Flag(vpiLocalParam, ParameterAt("top.b0", "BI")), 0);
  EXPECT_EQ(Flag(vpiLocalParam, ParameterAt("top.b1", "BQ")), 0);
}

TEST_F(ParameterPlacesOfARun, AnIfOrCaseGenerateBlocksParameterIsLocal) {
  Run(kPlaces);
  for (const char* scope : {"top.g", "top.c2"}) {
    SCOPED_TRACE(scope);
    const std::vector<std::string> kNames = NamesOf(vpiParameter, By(scope));
    ASSERT_FALSE(kNames.empty());
    for (const std::string& name : kNames) {
      EXPECT_EQ(Flag(vpiLocalParam, ParameterAt(scope, name)), 1) << name;
    }
    EXPECT_EQ(NamesOf(vpiVariables, By(scope)), std::vector<std::string>{});
  }
  EXPECT_EQ(NamesOf(vpiParameter, By("top.c2")),
            std::vector<std::string>{"CP"});
  EXPECT_EQ(By("top.c1"), nullptr);
}

TEST_F(ParameterPlacesOfARun,
       AnInterfacesOrProgramsGenerateBlocksParameterIsLocal) {
  Run(kPlaces);
  EXPECT_EQ(Flag(vpiLocalParam, ParameterAt("top.i0.g", "GP")), 1);
  EXPECT_EQ(Flag(vpiLocalParam, ParameterAt("top.p0.g", "GP")), 1);
  EXPECT_EQ(ValueOf(ParameterAt("top.i0.g", "GP")), 5);
  EXPECT_EQ(ValueOf(ParameterAt("top.p0.g", "GP")), 6);
}

}  // namespace
}  // namespace delta
