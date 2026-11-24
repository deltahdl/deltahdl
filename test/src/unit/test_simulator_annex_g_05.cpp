#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

namespace {

std::string RunIn(const std::string& scopes, const std::string& steps) {
  SimFixture f;
  return RunCapture(scopes +
                        "module t;\n"
                        "  int a;\n"
                        "  initial begin\n" +
                        steps + "  end\nendmodule\n",
                    f);
}

TEST(RandomizePrototypeRun, ACallReturnsOneFromAPackageFunction) {
  EXPECT_EQ(
      RunIn("package p;\n"
            "  function int draw();\n"
            "    int v;\n"
            "    return std::randomize(v) with { v == 6; } ? 10 + v : 0;\n"
            "  endfunction\n"
            "  function int status();\n"
            "    int v;\n"
            "    return std::randomize(v);\n"
            "  endfunction\n"
            "endpackage\n",
            "    $write(\"%0d %0d\", p::status(), p::draw());\n"),
      "1 16");
}

TEST(RandomizePrototypeRun, ACallReturnsOneFromAClassMethod) {
  EXPECT_EQ(RunIn("class c;\n"
                  "  int y;\n"
                  "  function int status();\n"
                  "    return std::randomize(y);\n"
                  "  endfunction\n"
                  "  function int impossible();\n"
                  "    return std::randomize(y) with { y < 2; y > 4; };\n"
                  "  endfunction\n"
                  "endclass\n",
                  "    c o;\n"
                  "    o = new;\n"
                  "    $write(\"%0d %0d\", o.status(), o.impossible());\n"),
            "1 0");
}

TEST(RandomizePrototypeRun, AResultIsThirtyTwoBits) {
  EXPECT_EQ(RunIn("", "    $write(\"%0d\", $bits(std::randomize(a)));\n"),
            "32");
}

TEST(RandomizePrototypeRun, DISABLED_AResultIsSignedInAModule) {
  EXPECT_EQ(RunIn("",
                  "    $write(\"%0d \", (std::randomize() - 2) < 0);\n"
                  "    $write(\"%0d\", std::randomize(a) - 2);\n"),
            "1 -1");
}

TEST(RandomizePrototypeRun, DISABLED_AResultIsSignedInAPackageFunction) {
  EXPECT_EQ(RunIn("package p;\n"
                  "  function bit below();\n"
                  "    int v;\n"
                  "    return (std::randomize(v) - 2) < 0;\n"
                  "  endfunction\n"
                  "endpackage\n",
                  "    $write(\"%0d\", p::below());\n"),
            "1");
}

TEST(RandomizePrototypeRun, DISABLED_AResultIsSignedInAClassMethod) {
  EXPECT_EQ(RunIn("class c;\n"
                  "  int y;\n"
                  "  function bit below();\n"
                  "    return (std::randomize(y) - 2) < 0;\n"
                  "  endfunction\n"
                  "endclass\n",
                  "    c o;\n"
                  "    o = new;\n"
                  "    $write(\"%0d\", o.below());\n"),
            "1");
}

}  // namespace
