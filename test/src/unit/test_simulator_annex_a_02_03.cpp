#include <gtest/gtest.h>

#include <string>

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

void ExpectListSum(const std::string& src, const char* var) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  LowerRunAndCheck(f, design, {{var, 123u}});
}

TEST(DeclarationListSim, AParamAssignmentListInAClassOrFunction) {
  ExpectListSum(
      "class c;\n"
      "  localparam int A = 1, B = 2, C = 3;\n"
      "endclass\n"
      "module t;\n"
      "  int r;\n"
      "  initial r = c::A * 100 + c::B * 10 + c::C;\n"
      "endmodule\n",
      "r");
  ExpectListSum(
      "module t;\n"
      "  function int f;\n"
      "    localparam int A = 1, B = 2, C = 3;\n"
      "    return A * 100 + B * 10 + C;\n"
      "  endfunction\n"
      "  int r;\n"
      "  initial r = f();\n"
      "endmodule\n",
      "r");
}

TEST(DeclarationListSim, AParamAssignmentListInAPackageOrCompilationUnit) {
  ExpectListSum(
      "package p;\n"
      "  localparam int A = 1, B = 2, C = 3;\n"
      "endpackage\n"
      "module t;\n"
      "  int r;\n"
      "  initial r = p::A * 100 + p::B * 10 + p::C;\n"
      "endmodule\n",
      "r");
  ExpectListSum(
      "localparam int A = 1, B = 2, C = 3;\n"
      "module t;\n"
      "  int r;\n"
      "  initial r = A * 100 + B * 10 + C;\n"
      "endmodule\n",
      "r");
}

TEST(DeclarationListSim, AParamAssignmentListInEachDesignElementBody) {
  for (const char* unit : {"interface", "program"}) {
    ExpectListSum(std::string(unit) +
                      " i;\n"
                      "  localparam int A = 1, B = 2, C = 3;\n"
                      "  int r;\n"
                      "  initial r = A * 100 + B * 10 + C;\n"
                      "end" +
                      unit +
                      "\n"
                      "module t;\n"
                      "  i u();\n"
                      "endmodule\n",
                  "u.r");
  }
  ExpectListSum(
      "module t;\n"
      "  if (1) begin : g\n"
      "    localparam int A = 1, B = 2, C = 3;\n"
      "  end\n"
      "  int r;\n"
      "  initial r = g.A * 100 + g.B * 10 + g.C;\n"
      "endmodule\n",
      "r");
}

}  // namespace
