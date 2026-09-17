#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A class C holding the members `decls` under the constraint block `c`,
// randomized `draws` times by an initial that counts the draws for which
// `holds` is true, as the design test/src/e2e/uniqueness_constraints.sv
// does, and displays the count.
std::string Design(const std::string& decls, const std::string& constraint,
                   int draws, const std::string& holds) {
  return "class C;\n" + decls + "  constraint c { " + constraint +
         " }\n"
         "endclass\n"
         "module t;\n"
         "  int held = 0;\n"
         "  initial begin\n"
         "    C o = new;\n"
         "    repeat (" +
         std::to_string(draws) +
         ") begin\n"
         "      void'(o.randomize());\n"
         "      if (" +
         holds +
         ") held++;\n"
         "    end\n"
         "    $display(\"%0d\", held);\n"
         "  end\n"
         "endmodule\n";
}

// 18.5.4: the clause's example on singular variables: with excluded held to
// 5 by another constraint, no member of the group beside it takes 5, so b
// and c drawn from 4 to 6 split 4 and 6 between them on every draw.
TEST(UniquenessConstraintsRun, TheExcludedValueLeavesTheOtherMembers) {
  SimFixture f;
  std::string out = RunCapture(
      Design("  rand byte b;\n"
             "  rand byte c;\n"
             "  rand byte excluded;\n",
             "b inside {[4:6]}; c inside {[4:6]}; unique {b, c, excluded}; "
             "excluded == 5;",
             64, "o.excluded == 5 && o.b != 5 && o.c != 5 && o.b + o.c == 10"),
      f);
  EXPECT_EQ(out, "64\n");
}

// 18.5.4: a singular member may be of real type, and the group holds no two
// members at the same value, so two reals each drawn from 1.0 and 2.0 are
// never alike. The solver compared the integral draws of a group only, so
// two real members drawn alike passed as distinct.
TEST(UniquenessConstraintsRun, RealMembersNeverDrawAlike) {
  SimFixture f;
  std::string out = RunCapture(
      Design("  rand real r1;\n"
             "  rand real r2;\n",
             "r1 dist { 1.0 := 1, 2.0 := 1 }; r2 dist { 1.0 := 1, 2.0 := 1 }; "
             "unique {r1, r2};",
             64, "o.r1 != o.r2 && o.r1 + o.r2 == 3.0"),
      f);
  EXPECT_EQ(out, "64\n");
}

// 18.5.4: a group of fewer than two members has no effect and causes no
// contradiction, so randomize() succeeds beside a relation fixing the one
// member and the member takes the fixed value rather than keeping the 0 a
// failed randomize() would leave it.
TEST(UniquenessConstraintsRun, AGroupOfOneMemberHasNoEffect) {
  SimFixture f;
  std::string out = RunCapture(
      Design("  rand bit [3:0] x;\n", "x == 7; unique {x};", 32, "o.x == 7"),
      f);
  EXPECT_EQ(out, "32\n");
}

}  // namespace
