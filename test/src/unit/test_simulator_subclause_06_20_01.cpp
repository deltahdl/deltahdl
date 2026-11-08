#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ParameterArraySim, PositionalPatternFillsTheElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter int A[4] = '{1, 2, 3, 4};\n"
                       "  initial $display(\"%0d %0d\", A[1], A[3]);\n"
                       "endmodule\n",
                       f),
            "2 4\n");
}

TEST(ParameterArraySim, DescendingDimensionTakesItemsFromTheLeft) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  localparam int D[3:0] = '{1, 2, 3, 4};\n"
                       "  initial $display(\"%0d %0d\", D[3], D[0]);\n"
                       "endmodule\n",
                       f),
            "1 4\n");
}

TEST(ParameterArraySim, NestedPatternFillsTwoDimensions) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter int M[2][2] = '{'{1, 2}, '{3, 4}};\n"
                       "  initial $display(\"%0d %0d\", M[0][1], M[1][0]);\n"
                       "endmodule\n",
                       f),
            "2 3\n");
}

TEST(ParameterArraySim, DefaultKeyFillsEveryElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter int K[3] = '{default: 7};\n"
                       "  initial $display(\"%0d %0d\", K[0], K[2]);\n"
                       "endmodule\n",
                       f),
            "7 7\n");
}

TEST(ParameterArraySim, RealElementsKeepTheirFractions) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter real R[2] = '{1.5, 0.25};\n"
                       "  initial $display(\"%g %g\", R[0], R[1]);\n"
                       "endmodule\n",
                       f),
            "1.5 0.25\n");
}

TEST(ParameterArraySim, ParameterPortArrayFillsTheElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t #(parameter int A[2] = '{1, 2});\n"
                       "  initial $display(\"%0d %0d\", A[0], A[1]);\n"
                       "endmodule\n",
                       f),
            "1 2\n");
}

TEST(ParameterArraySim, ClauseExampleReadsAPartSelectOfAnElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter logic [31:0] P1 [3:0] = '{1, 2, 3, 4};\n"
                       "  initial begin\n"
                       "    if (P1[2][7:0])\n"
                       "      $display(\"%0d %0d\", P1[2][7:0], P1[0][7:0]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "2 4\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ParameterArraySim, PartSelectOfAnElementTakesThatElementsBits) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  parameter logic [31:0] P1 [3:0] =\n"
                 "      '{32'h1, 32'h2A3B, 32'h3, 32'h4};\n"
                 "  initial $display(\"%h %h\", P1[2][7:0], P1[2][15:8]);\n"
                 "endmodule\n",
                 f),
      "3b 2a\n");
  EXPECT_FALSE(f.has_errors);
}

uint64_t ValueOf(SimFixture& f, std::string_view name) {
  const Variable* v = f.ctx.FindVariable(name);
  EXPECT_NE(v, nullptr) << name;
  return v == nullptr ? ~uint64_t{0} : v->value.ToUint64();
}

TEST(ParameterArraySim, WholeArrayDefparamGivesEveryElement) {
  SimFixture f;
  RunAndFindVar(
      "module sub;\n"
      "  parameter int A[2] = '{1, 2};\n"
      "  int x, y;\n"
      "  initial begin\n"
      "    x = A[0];\n"
      "    y = A[1];\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  sub u();\n"
      "  sub d();\n"
      "  defparam u.A = '{5, 6};\n"
      "endmodule\n",
      f, "u.x");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ValueOf(f, "u.x"), 5u);
  EXPECT_EQ(ValueOf(f, "u.y"), 6u);
  EXPECT_EQ(ValueOf(f, "d.x"), 1u);
  EXPECT_EQ(ValueOf(f, "d.y"), 2u);
}

TEST(StructureParameterSim, MembersReadTheDefaultOrTheWholeOverride) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int a; logic [7:0] b; } s_t;\n"
      "module m #(parameter s_t P = '{a: 1, b: 8'h2});\n"
      "  int a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a = P.a;\n"
      "    b = P.b;\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  m d();\n"
      "  m #(.P('{a: 5, b: 8'h6})) u();\n"
      "  m #('{a: 7, b: 8'h8}) v();\n"
      "endmodule\n",
      f, "d.a");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ValueOf(f, "d.a"), 1u);
  EXPECT_EQ(ValueOf(f, "d.b"), 2u);
  EXPECT_EQ(ValueOf(f, "u.a"), 5u);
  EXPECT_EQ(ValueOf(f, "u.b"), 6u);
  EXPECT_EQ(ValueOf(f, "v.a"), 7u);
  EXPECT_EQ(ValueOf(f, "v.b"), 8u);
}

TEST(StructureParameterSim, BodyParameterAndLocalparamMembersAreRead) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int a; logic [7:0] b; } s_t;\n"
                       "module t;\n"
                       "  parameter s_t Q = '{a: 3, b: 8'h4};\n"
                       "  localparam s_t L = '{b: 8'h9, a: 10};\n"
                       "  initial $display(\"%0d %0d %0d %0d\", Q.a, Q.b, "
                       "L.a, L.b);\n"
                       "endmodule\n",
                       f),
            "3 4 10 9\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(StructureParameterSim, WholeStructureDefparamGivesEveryMember) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int a; logic [7:0] b; } s_t;\n"
      "module sub;\n"
      "  parameter s_t P = '{a: 1, b: 8'h2};\n"
      "  int a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a = P.a;\n"
      "    b = P.b;\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  sub u();\n"
      "  sub d();\n"
      "  defparam u.P = '{a: 9, b: 8'h3};\n"
      "endmodule\n",
      f, "u.a");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ValueOf(f, "u.a"), 9u);
  EXPECT_EQ(ValueOf(f, "u.b"), 3u);
  EXPECT_EQ(ValueOf(f, "d.a"), 1u);
  EXPECT_EQ(ValueOf(f, "d.b"), 2u);
}

TEST(StructureParameterSim, MemberOfAnElementOfAStructureArrayIsRead) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int a; logic [7:0] b; } s_t;\n"
                       "module t;\n"
                       "  parameter s_t S [2] =\n"
                       "      '{'{a: 1, b: 8'h2}, '{a: 3, b: 8'h4}};\n"
                       "  initial $display(\"%0d %0d\", S[1].a, S[0].b);\n"
                       "endmodule\n",
                       f),
            "3 2\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(StructureParameterSim, MembersAreReadInAGenerateBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int a; logic [7:0] b; } s_t;\n"
                       "module t;\n"
                       "  if (1) begin : g\n"
                       "    localparam s_t G = '{a: 17, b: 8'h18};\n"
                       "    localparam int A[2] = '{19, 20};\n"
                       "    initial $display(\"%0d %0d %0d\", G.a, G.b, "
                       "A[1]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "17 24 20\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(StructureParameterSim, MembersAreReadFromAPackageAndTheUnit) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int a; logic [7:0] b; } s_t;\n"
                       "parameter s_t U = '{a: 11, b: 8'h12};\n"
                       "package pk;\n"
                       "  parameter s_t K = '{a: 13, b: 8'h14};\n"
                       "  parameter int A[2] = '{15, 16};\n"
                       "endpackage\n"
                       "module t;\n"
                       "  initial $display(\"%0d %0d %0d %0d %0d\", U.a, U.b, "
                       "pk::K.a, pk::K.b, pk::A[1]);\n"
                       "endmodule\n",
                       f),
            "11 18 13 20 16\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(StructureParameterSim, MembersAreReadInAClass) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int a; logic [7:0] b; } s_t;\n"
                       "class C;\n"
                       "  localparam s_t K = '{a: 19, b: 8'h1A};\n"
                       "  localparam int A[2] = '{21, 22};\n"
                       "  static function int f();\n"
                       "    return K.a + A[1];\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial $display(\"%0d %0d\", C::f(), C::K.b);\n"
                       "endmodule\n",
                       f),
            "41 26\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(StructureParameterSim, MembersAreReadInAnInterface) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int a; logic [7:0] b; } s_t;\n"
      "interface ifc #(parameter s_t P = '{a: 1, b: 8'h2});\n"
      "  int a;\n"
      "  initial a = P.a + P.b;\n"
      "endinterface\n"
      "module t;\n"
      "  ifc #(.P('{a: 30, b: 8'h5})) i();\n"
      "  ifc d();\n"
      "endmodule\n",
      f, "i.a");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ValueOf(f, "i.a"), 35u);
  EXPECT_EQ(ValueOf(f, "d.a"), 3u);
}

}  // namespace
