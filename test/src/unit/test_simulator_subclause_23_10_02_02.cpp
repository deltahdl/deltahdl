#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StringParamOverride,
     ANamedOverrideLongerThanFourCharactersKeepsEveryCharacter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child #(parameter string NAME = \"x\") ();\n"
                       "  initial $display(\"%s\", NAME);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  child #(.NAME(\"John Smith\")) u();\n"
                       "endmodule\n",
                       f),
            "John Smith\n");
}

TEST(StringParamOverride,
     ANamedOverrideOfExactlyFiveCharactersKeepsEveryCharacter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child #(parameter string NAME = \"x\") ();\n"
                       "  initial $display(\"%s\", NAME);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  child #(.NAME(\"hello\")) u();\n"
                       "endmodule\n",
                       f),
            "hello\n");
}

TEST(StringParamOverride, ANamedOverrideOfNineCharactersKeepsEveryCharacter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child #(parameter string NAME = \"x\") ();\n"
                       "  initial $display(\"%s\", NAME);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  child #(.NAME(\"resolvers\")) u();\n"
                       "endmodule\n",
                       f),
            "resolvers\n");
}

TEST(StringParamOverride,
     AnOverriddenStringParameterIsRegisteredAsAStringVariable) {
  SimFixture f;
  Variable* p = RunAndFindVar(
      "module child #(parameter string NAME = \"x\") ();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.NAME(\"John Smith\")) u();\n"
      "endmodule\n",
      f, "u.NAME");
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(f.ctx.IsStringVariable("u.NAME"));
}

TEST(StringParamOverride,
     ANamedOverrideNamingAnotherParameterKeepsEveryCharacter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child #(parameter string NAME = \"x\") ();\n"
                       "  initial $display(\"%s\", NAME);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  parameter string WANTED = \"John Smith\";\n"
                       "  child #(.NAME(WANTED)) u();\n"
                       "endmodule\n",
                       f),
            "John Smith\n");
}

TEST(NamedParamAssignment, RealOverrideTakesTheParametersTypeOrGivesItsOwn) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m #(parameter Q = 5, parameter real R = 1.5,\n"
                       "           parameter S = \"abc\")();\n"
                       "  initial #1 $display(\"Q %f R %f S %s bitsQ %0d\",\n"
                       "                      Q, R, S, $bits(Q));\n"
                       "endmodule\n"
                       "module top;\n"
                       "  m #(.Q(2.5), .R(3.25), .S(\"xyz\")) u();\n"
                       "  m #(7) v();\n"
                       "endmodule\n",
                       f),
            "Q 2.500000 R 3.250000 S xyz bitsQ 64\n"
            "Q 7.000000 R 1.500000 S abc bitsQ 32\n");
}

TEST(NamedParamAssignment, RealOverrideBesideRangedAndIntegralOverrides) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m #(parameter [3:0] P = 0, parameter Q = 5,\n"
                       "           parameter signed [3:0] S = 0,\n"
                       "           parameter real R = 1.5)();\n"
                       "  initial #1 $display(\"p %0d q %f s %0d r %f\",\n"
                       "                      P, Q, S, R);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  m #(.P(20), .Q(2.5), .S(15), .R(3)) u();\n"
                       "endmodule\n",
                       f),
            "p 4 q 2.500000 s -1 r 3.000000\n");
}

TEST(NamedParamAssignment, AssignmentPatternOverridesAnArrayParameter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub;\n"
                       "  parameter int A[2] = '{1, 2};\n"
                       "  initial #1 $display(\"%0d %0d\", A[0], A[1]);\n"
                       "endmodule\n"
                       "module sp #(parameter int P[2] = '{1, 2});\n"
                       "  initial #2 $display(\"%0d %0d\", P[0], P[1]);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  sub #(.A('{5, 6})) u();\n"
                       "  sp #(.P('{7, 8})) v();\n"
                       "endmodule\n",
                       f),
            "5 6\n7 8\n");
}

TEST(NamedParamAssignment, ArrayParameterOverrideReadsTheInstantiatingScope) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub;\n"
                       "  parameter int K = 1;\n"
                       "  parameter int A[2] = '{1, 2};\n"
                       "  initial $display(\"%0d %0d\", A[0], A[1]);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  parameter int K = 9;\n"
                       "  sub #(.A('{K, K + 1})) u();\n"
                       "endmodule\n",
                       f),
            "9 10\n");
}

}  // namespace
