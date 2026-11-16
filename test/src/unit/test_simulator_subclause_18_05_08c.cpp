#include <gtest/gtest.h>

#include <string>

#include "helpers_constraint_places.h"

using namespace delta;

namespace {

const char* const kAll = "16\n";
const char* const kLeaf = "class A; rand bit [3:0] v; endclass\n";
const char* const kPinnedLeaf =
    "class A; rand bit [3:0] v; constraint bad { v == 3; } endclass\n";

TEST(GlobalConstraintCases, AnOutOfBlockGlobalConstraintHolds) {
  EXPECT_EQ(CountHeld(Tally(kLeaf,
                            "  rand A a = new;\n"
                            "  int c = 5;\n"
                            "  constraint k;\n",
                            "constraint C::k { a.v > c; }\n", "o.randomize()",
                            "o.a.v > 5")),
            kAll);
}

TEST(GlobalConstraintCases, AnInlineGlobalConstraintHolds) {
  EXPECT_EQ(CountHeld(Tally(kLeaf,
                            "  rand A a = new;\n"
                            "  int c = 5;\n",
                            "", "o.randomize() with { a.v == c + 1; }",
                            "o.a.v == 6")),
            kAll);
}

TEST(GlobalConstraintCases, AnObjectUnderANonRandHandleIsLeftOut) {
  EXPECT_EQ(CountHeld(Tally(kPinnedLeaf,
                            "  A a = new;\n"
                            "  rand bit [3:0] x;\n"
                            "  constraint g { x == a.v; }\n"
                            "  function new(); a.v = 9; endfunction\n",
                            "", "o.randomize()", "o.a.v == 9 && o.x == 9")),
            kAll);
}

TEST(GlobalConstraintCases, AnObjectUnderARandHandleIsSolved) {
  EXPECT_EQ(CountHeld(Tally(kPinnedLeaf,
                            "  rand A a = new;\n"
                            "  function new(); a.v = 9; endfunction\n",
                            "", "o.randomize()", "o.a.v == 3")),
            kAll);
}

TEST(GlobalConstraintCases, AMemberObjectsEnabledConstraintConflicts) {
  EXPECT_EQ(CountHeld(Tally(kPinnedLeaf,
                            "  rand A a = new;\n"
                            "  constraint c { a.v != 3; }\n",
                            "", "o.randomize() == 0", "1")),
            kAll);
}

std::string ModeRun(const char* c_items, const char* mode_call,
                    const char* check) {
  return CountHeld(std::string(kPinnedLeaf) + "class C; rand A a = new; " +
                   c_items +
                   " endclass\n"
                   "module t;\n"
                   "  int n, held = 0;\n"
                   "  initial begin\n"
                   "    static C o = new;\n"
                   "    o.a.v = 9;\n" +
                   mode_call +
                   "    for (n = 0; n < 16; n++)\n"
                   "      if (o.randomize() && (" +
                   check +
                   ")) held++;\n"
                   "    $display(\"%0d\", held);\n"
                   "  end\n"
                   "endmodule\n");
}

TEST(GlobalConstraintCases, AMemberObjectsDisabledConstraintIsNotApplied) {
  EXPECT_EQ(ModeRun("constraint c { a.v != 3; }",
                    "    o.a.bad.constraint_mode(0);\n", "o.a.v != 3"),
            kAll);
}

TEST(GlobalConstraintCases, AHandleTurnedOffByRandModeLeavesItsObjectOut) {
  EXPECT_EQ(ModeRun("", "    o.a.rand_mode(0);\n", "o.a.v == 9"), kAll);
}

TEST(GlobalConstraintCases, AHandleLeftOnSolvesItsObject) {
  EXPECT_EQ(ModeRun("", "", "o.a.v == 9"), "0\n");
}

}  // namespace
