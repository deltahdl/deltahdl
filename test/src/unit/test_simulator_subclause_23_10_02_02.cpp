#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// IEEE 1800-2023 6.16 rules that a string value is of arbitrary length and is
// never truncated. "John Smith" is ten characters, so a named override that
// carries the value as an integer keeps only its low bytes and displays the
// tail of the string rather than the whole of it.
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

// Five characters is the first length a 32-bit override value cannot hold, so
// "hello" is the shortest string that distinguishes a widened value from a
// truncated one. An override routed through a 32-bit integer displays "ello".
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

// Nine characters is the first length an int64_t cannot hold, so "resolvers"
// separates a fix that widened the override value from one that stopped
// routing the characters through an integer at all. A 64-bit value displays
// "esolvers".
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

// An override must leave the parameter typed as a string, not as the integer
// the value travelled in. SimContext::IsStringVariable answers false when the
// override registered u.NAME as a plain vector, which is how a run displays
// the characters as a number even when every one of them survived.
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

// §23.10.2 admits a constant expression as an instance parameter value
// assignment, and §11.2.1 makes a parameter one of the operands such an
// expression consists of. The name is written in the instantiating module, so
// its characters are the parent's to supply; a fold that took only a literal
// left NAME holding the packed number and displayed "mith".
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

// §23.10 (printed page 764): "An override value shall be converted to the
// type of the parameter", so `.R(3.25)` on `parameter real R` makes R 3.25;
// and a parameter with neither type nor range takes "the type and range of
// the new value", so `.Q(2.5)` makes Q the real 2.5, 64 bits. A real
// override was folded as an integer, had no value and was dropped: R kept
// 1.5 and Q read 0.0. The instance with no real override keeps Q integral.
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

// The same beside ranged parameters, which keep their range: 20 into
// [3:0] P is 4, and a signed [3:0] S reads 15 as -1. An integral override
// of a parameter declared real is a real, `.R(3)` reading 3.0.
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

}  // namespace
