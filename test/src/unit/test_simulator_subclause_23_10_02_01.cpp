#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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
