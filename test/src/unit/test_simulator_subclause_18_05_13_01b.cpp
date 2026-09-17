#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.5.13.1: the clause's example, a D2 holding two D1 and a B1 randomized
// with an inline block of two soft constraints. Reinstated from the highest
// priority down while the set stays satisfiable, the inline y inside {10,
// 20, 30} and y < p1.x hold, e1 and d1 contradict them and are discarded,
// c1 leaves y at 20 or 30, p3 keeps its [5:9] and loses a1, p2 keeps both
// bounds, and p1 loses its [5:9], no value of it lying above y, and keeps
// its bounds: over 8 draws y is 20 or 30 below p1.x, p1.x below p2.x below
// 100, and p3.x in 5 to 9, as the design
// test/src/e2e/soft_constraint_priorities.sv runs it.
TEST(SoftConstraintPrioritiesRun, TheClausesExampleResolvesByPriority) {
  SimFixture f;
  std::string out = RunCapture(
      "class B1;\n"
      "  rand int x;\n"
      "  constraint a { soft x > 10; soft x < 100; }\n"
      "endclass\n"
      "class D1 extends B1;\n"
      "  constraint b { soft x inside {[5:9]}; }\n"
      "endclass\n"
      "class B2;\n"
      "  rand int y;\n"
      "  constraint c { soft y > 10; }\n"
      "endclass\n"
      "class D2 extends B2;\n"
      "  constraint d { soft y inside {[5:9]}; }\n"
      "  constraint e;\n"
      "  rand D1 p1;\n"
      "  rand B1 p2;\n"
      "  rand D1 p3;\n"
      "  constraint f { soft p1.x < p2.x; }\n"
      "endclass\n"
      "constraint D2::e { soft y > 100; }\n"
      "module t;\n"
      "  int ok = 0, picked = 0, ordered = 0, third = 0;\n"
      "  initial begin\n"
      "    D2 d = new;\n"
      "    d.p1 = new;\n"
      "    d.p2 = new;\n"
      "    d.p3 = new;\n"
      "    repeat (8) begin\n"
      "      if (d.randomize() with { soft y inside {10, 20, 30}; soft y < "
      "p1.x; })\n"
      "        ok++;\n"
      "      if (d.y == 20 || d.y == 30) picked++;\n"
      "      if (d.y < d.p1.x && d.p1.x < d.p2.x && d.p2.x < 100) ordered++;\n"
      "      if (d.p3.x >= 5 && d.p3.x <= 9) third++;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d %0d\", ok, picked, ordered, third);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8 8 8 8\n");
}

// 18.5.13.1: a constraint in an external block has the priority of its
// prototype's place in the class, not the out-of-body block's: the
// prototype declared after the block preferring 1 outranks it, so the
// external block's 2 prevails.
TEST(SoftConstraintPrioritiesRun, AnExternalBlockTakesItsPrototypesPlace) {
  SimFixture f;
  std::string out = RunCapture(
      "class Ext;\n"
      "  rand int v;\n"
      "  constraint early { soft v == 1; }\n"
      "  constraint late;\n"
      "endclass\n"
      "constraint Ext::late { soft v == 2; }\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    Ext x = new;\n"
      "    ok = x.randomize();\n"
      "    $display(\"%0d %0d\", ok, x.v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2\n");
}

// 18.5.13.1: the constraints in a contained object have lower priority than
// all constraints in its container, and the object whose handle is declared
// later outranks the one before it: the container ties the two values, the
// later object prefers 2 and the earlier 1, so both take 2.
TEST(SoftConstraintPrioritiesRun, TheContainerAndTheLaterHandleOutrank) {
  SimFixture f;
  std::string out = RunCapture(
      "class Early;\n"
      "  rand int v;\n"
      "  constraint c { soft v == 1; }\n"
      "endclass\n"
      "class Late;\n"
      "  rand int v;\n"
      "  constraint c { soft v == 2; }\n"
      "endclass\n"
      "class Both;\n"
      "  rand Early e;\n"
      "  rand Late l;\n"
      "  constraint tie { soft e.v == l.v; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    Both b = new;\n"
      "    b.e = new;\n"
      "    b.l = new;\n"
      "    ok = b.randomize();\n"
      "    $display(\"%0d %0d %0d\", ok, b.e.v, b.l.v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 2\n");
}

}  // namespace
