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

}  // namespace
