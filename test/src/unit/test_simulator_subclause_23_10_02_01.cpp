#include "fixture_simulator.h"

using namespace delta;

namespace {

// IEEE 1800-2023 6.16 rules that a string value is never truncated, and
// 23.10.2.1 gives the ordered form of the override its own fold site,
// separate from the by-name form of 23.10.2.2. "John Smith" is ten
// characters, so an ordered override that carries the value as an integer
// displays only the tail of the string.
TEST(StringParamOverride, APositionalOverrideKeepsEveryCharacter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child #(parameter string NAME = \"x\") ();\n"
                       "  initial $display(\"%s\", NAME);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  child #(\"John Smith\") u();\n"
                       "endmodule\n",
                       f),
            "John Smith\n");
}

// Nine characters is the first length an int64_t cannot hold, so "resolvers"
// fails on an ordered override whose value was merely widened rather than
// kept out of an integer. A 64-bit value displays "esolvers".
TEST(StringParamOverride,
     APositionalOverrideOfNineCharactersKeepsEveryCharacter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child #(parameter string NAME = \"x\") ();\n"
                       "  initial $display(\"%s\", NAME);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  child #(\"resolvers\") u();\n"
                       "endmodule\n",
                       f),
            "resolvers\n");
}

// The positional form of the same override. §23.10.2.1 resolves an ordered
// list at a site of its own from the named one, so a repair reaching only the
// named path would leave this displaying "mith".
TEST(StringParamOverride,
     APositionalOverrideNamingAnotherParameterKeepsEveryCharacter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child #(parameter string NAME = \"x\") ();\n"
                       "  initial $display(\"%s\", NAME);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  parameter string WANTED = \"John Smith\";\n"
                       "  child #(WANTED) u();\n"
                       "endmodule\n",
                       f),
            "John Smith\n");
}

}  // namespace
