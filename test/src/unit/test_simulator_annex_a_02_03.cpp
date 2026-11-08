#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(DeclarationListSim, MultipleVarDeclInitializersApplyIndependently) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a = 8'd11, b = 8'd22, c = 8'd33;\n"
      "  logic [7:0] ra, rb, rc;\n"
      "  initial begin\n"
      "    ra = a; rb = b; rc = c;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"ra", 11u}, {"rb", 22u}, {"rc", 33u}});
}

TEST(DeclarationListSim, VarDeclListInitializedFromParameter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int P = 5;\n"
      "  logic [7:0] a = P, b = P + 8'd10;\n"
      "  logic [7:0] ra, rb;\n"
      "  initial begin\n"
      "    ra = a; rb = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"ra", 5u}, {"rb", 15u}});
}

TEST(DeclarationListSim, VarDeclListInitializedFromLocalparam) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int Q = 7;\n"
      "  logic [7:0] a = Q, b = Q + 8'd1;\n"
      "  logic [7:0] ra, rb;\n"
      "  initial begin\n"
      "    ra = a; rb = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"ra", 7u}, {"rb", 8u}});
}

TEST(DeclarationListSim, MultipleParamAssignmentsUsableAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter A = 3, B = 4, C = 5;\n"
      "  logic [7:0] r;\n"
      "  initial r = A + B + C;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 12u}});
}

}  // namespace
