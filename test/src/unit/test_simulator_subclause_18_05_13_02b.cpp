#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The clause's C over random p and q: p gates the soft q of c_1 without
// appearing in it, and c_2 prefers p; the directive of c_3 is completed by
// each case.
const char* const kGatedHead =
    "class C;\n"
    "  rand bit p;\n"
    "  rand bit q;\n"
    "  constraint c_1 { p -> soft q; }\n"
    "  constraint c_2 { soft p; }\n";

// 18.5.13.2: a 'disable soft' directive discards only the soft constraints
// the variable directly appears in. disable soft p discards c_2, where p
// appears, and not c_1, which p only gates, so over 32 draws p comes up
// clear in some and q is set whenever p is, as the design
// test/src/e2e/disabling_soft_constraints.sv runs it.
TEST(DisablingSoftConstraintsRun, TheGateOfASoftConsequentIsNoReference) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kGatedHead) +
          "  constraint c_3 { disable soft p; }\n"
          "endclass\n"
          "module t;\n"
          "  int sets = 0, gated = 0;\n"
          "  initial begin\n"
          "    C c = new;\n"
          "    repeat (32) begin\n"
          "      void'(c.randomize());\n"
          "      if (c.p) sets++;\n"
          "      if (!c.p || c.q) gated++;\n"
          "    end\n"
          "    $display(\"%0d %0d\", sets > 0 && sets < 32, gated);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "1 32\n");
}

// 18.5.13.2: disable soft q discards c_1, the soft constraint q appears in,
// and leaves c_2, so p is set on every draw and q is drawn free, clear in
// some.
TEST(DisablingSoftConstraintsRun, ADirectiveOnTheConsequentDiscardsTheGated) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kGatedHead) +
                     "  constraint c_3 { disable soft q; }\n"
                     "endclass\n"
                     "module t;\n"
                     "  int sets = 0, clears = 0;\n"
                     "  initial begin\n"
                     "    C c = new;\n"
                     "    repeat (32) begin\n"
                     "      void'(c.randomize());\n"
                     "      if (c.p) sets++;\n"
                     "      if (!c.q) clears++;\n"
                     "    end\n"
                     "    $display(\"%0d %0d\", sets, clears > 0);\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "32 1\n");
}

// 18.5.13.2: the clause's A. The directive of A2 discards A1, the
// lower-priority preference for 3, and not A3, declared after it, so x
// takes 1 and 2, both over 32 draws.
TEST(DisablingSoftConstraintsRun, TheClausesADrawsTheLaterMembership) {
  SimFixture f;
  std::string out = RunCapture(
      "class A;\n"
      "  rand int x;\n"
      "  constraint A1 { soft x == 3; }\n"
      "  constraint A2 { disable soft x; }\n"
      "  constraint A3 { soft x inside {1, 2}; }\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0, ones = 0, twos = 0;\n"
      "  initial begin\n"
      "    A a = new;\n"
      "    repeat (32) begin\n"
      "      void'(a.randomize());\n"
      "      if (a.x == 1 || a.x == 2) held++;\n"
      "      if (a.x == 1) ones++;\n"
      "      if (a.x == 2) twos++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", held, ones > 0 && twos > 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 1\n");
}

}  // namespace
