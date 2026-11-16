#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunSrc(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

const char* const kPinned =
    "class P;\n"
    "  rand bit [3:0] x;\n"
    "  static constraint c_pin { x == 3; }\n"
    "  function void off_this(); this.c_pin.constraint_mode(0); endfunction\n"
    "  function void off_bare(); c_pin.constraint_mode(0); endfunction\n"
    "endclass\n"
    "class Q extends P;\n"
    "  static constraint c_low { x < 2; }\n"
    "endclass\n";

std::string Freed(const std::string& decls, const std::string& turn_off,
                  const std::string& other) {
  return std::string(kPinned) +
         "module t;\n"
         "  int n, freed = 0;\n"
         "  initial begin\n" +
         decls + turn_off +
         "    for (n = 0; n < 32; n++)\n"
         "      if (" +
         other + ".randomize() && " + other +
         ".x != 3) freed++;\n"
         "    $display(\"%0d %0d\", " +
         other +
         ".c_pin.constraint_mode(), freed > 0);\n"
         "  end\n"
         "endmodule\n";
}

const char* const kTwoP =
    "    static P p1 = new;\n"
    "    static P p2 = new;\n";

TEST(StaticConstraintCases, AnObjectLevelCallTurnsTheStaticBlockOffForOthers) {
  EXPECT_EQ(RunSrc(Freed(kTwoP, "    p1.constraint_mode(0);\n", "p2")),
            "0 1\n");
}

TEST(StaticConstraintCases, AThisQualifiedCallInAMethodReachesOtherObjects) {
  EXPECT_EQ(RunSrc(Freed(kTwoP, "    p1.off_this();\n", "p2")), "0 1\n");
}

TEST(StaticConstraintCases,
     DISABLED_AnUnqualifiedCallInAMethodReachesOtherObjects) {
  EXPECT_EQ(RunSrc(Freed(kTwoP, "    p1.off_bare();\n", "p2")), "0 1\n");
}

TEST(StaticConstraintCases, DISABLED_AnUnqualifiedCallInAMethodReachesItsOwn) {
  EXPECT_EQ(RunSrc(Freed(kTwoP, "    p1.off_bare();\n", "p1")), "0 1\n");
}

TEST(StaticConstraintCases, ABaseObjectAndADerivedObjectShareTheBaseBlock) {
  EXPECT_EQ(RunSrc(Freed("    static P p1 = new;\n"
                         "    static P p2;\n"
                         "    static Q q = new;\n",
                         "    p2 = q;\n"
                         "    p1.c_pin.constraint_mode(0);\n",
                         "p2")),
            "0 1\n");
}

TEST(StaticConstraintCases, AStaticBlockOfADerivedClassIsSharedByItsObjects) {
  EXPECT_EQ(RunSrc(std::string(kPinned) +
                   "module t;\n"
                   "  int n, high = 0;\n"
                   "  initial begin\n"
                   "    static Q q1 = new;\n"
                   "    static Q q2 = new;\n"
                   "    q1.c_pin.constraint_mode(0);\n"
                   "    q1.c_low.constraint_mode(0);\n"
                   "    for (n = 0; n < 32; n++)\n"
                   "      if (q2.randomize() && q2.x >= 2) high++;\n"
                   "    $display(\"%0d %0d\", q2.c_low.constraint_mode(), "
                   "high > 0);\n"
                   "  end\n"
                   "endmodule\n"),
            "0 1\n");
}

TEST(StaticConstraintCases, AStaticBlockOfADerivedClassHoldsWhileOn) {
  EXPECT_EQ(RunSrc(std::string(kPinned) +
                   "module t;\n"
                   "  int n, low = 0;\n"
                   "  initial begin\n"
                   "    static Q q1 = new;\n"
                   "    static Q q2 = new;\n"
                   "    q1.c_pin.constraint_mode(0);\n"
                   "    for (n = 0; n < 32; n++)\n"
                   "      if (q2.randomize() && q2.x < 2) low++;\n"
                   "    $display(\"%0d %0d\", q2.c_low.constraint_mode(), "
                   "low);\n"
                   "  end\n"
                   "endmodule\n"),
            "1 32\n");
}

}  // namespace
