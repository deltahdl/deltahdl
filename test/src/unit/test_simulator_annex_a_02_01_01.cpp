#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ParameterDeclarationScopes, AClassTakesAValueAndATypeParameter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class c;\n"
      "  parameter int B = 2;\n"
      "  localparam type U = bit [2:0];\n"
      "endclass\n"
      "module t;\n"
      "  c::U u;\n"
      "  int rb, ru;\n"
      "  initial begin rb = c::B; ru = $bits(u); end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"rb", 2u}, {"ru", 3u}});
}

TEST(ParameterDeclarationScopes, AFunctionTakesAValueAndATypeParameter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function int f;\n"
      "    localparam int F = 6;\n"
      "    localparam type W = bit [4:0];\n"
      "    W w;\n"
      "    return F * 10 + $bits(w);\n"
      "  endfunction\n"
      "  int r;\n"
      "  initial r = f();\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 65u}});
}

TEST(ParameterDeclarationScopes,
     APackageValueParameterIsReadThroughItsPackage) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int A = 1;\n"
      "  localparam type T = bit [5:0];\n"
      "endpackage\n"
      "module t;\n"
      "  int r;\n"
      "  initial r = p::A;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 1u}});
}

TEST(ParameterDeclarationScopes, DISABLED_APackageTypeParameterTypesAVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  localparam type T = bit [5:0];\n"
      "endpackage\n"
      "module t;\n"
      "  p::T v;\n"
      "  int r;\n"
      "  initial r = $bits(v);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 6u}});
}

TEST(ParameterDeclarationScopes, InterfaceAndProgramParametersOfImplicitType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface i;\n"
      "  parameter [3:0] D = 4;\n"
      "  localparam signed E = 5;\n"
      "  int r;\n"
      "  initial r = D * 10 + E;\n"
      "endinterface\n"
      "program q;\n"
      "  parameter [3:0] D = 6;\n"
      "  localparam signed E = 7;\n"
      "  int r;\n"
      "  initial r = D * 10 + E;\n"
      "endprogram\n"
      "module t;\n"
      "  i u0();\n"
      "  q u1();\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"u0.r", 45u}, {"u1.r", 67u}});
}

TEST(ParameterDeclarationScopes, AGenerateBlockParameterIsReadThroughTheBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  if (1) begin : g\n"
      "    localparam int G = 7;\n"
      "    localparam type GT = bit [1:0];\n"
      "    GT v;\n"
      "  end\n"
      "  int rg, rv;\n"
      "  initial begin rg = g.G; rv = $bits(g.v); end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"rg", 7u}, {"rv", 2u}});
}

TEST(ParameterDeclarationScopes,
     ACompilationUnitValueParameterIsReadByAModule) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "localparam int CU = 3;\n"
      "module t;\n"
      "  int r;\n"
      "  initial r = CU;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 3u}});
}

TEST(ParameterDeclarationScopes,
     DISABLED_ACompilationUnitTypeParameterTypesAVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "parameter type CT = byte;\n"
      "module t;\n"
      "  CT v;\n"
      "  int r;\n"
      "  initial r = $bits(v);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 8u}});
}

}  // namespace
