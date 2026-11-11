#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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
      "    static D2 d = new;\n"
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
      "    static Ext x = new;\n"
      "    ok = x.randomize();\n"
      "    $display(\"%0d %0d\", ok, x.v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2\n");
}

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
      "    static Both b = new;\n"
      "    b.e = new;\n"
      "    b.l = new;\n"
      "    ok = b.randomize();\n"
      "    $display(\"%0d %0d %0d\", ok, b.e.v, b.l.v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 2\n");
}

TEST(SoftConstraintPrioritiesRun, MixedSignRelationKeptBesideALaterEquality) {
  SimFixture f;
  std::string out = RunCapture(
      "class M;\n"
      "  rand int x;\n"
      "  rand bit [7:0] y;\n"
      "  constraint c { x inside {[-1:4]}; soft x > y; soft y == 200; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok = 0, neg = 0, two = 0;\n"
      "  initial begin\n"
      "    static M m = new;\n"
      "    repeat (8) begin\n"
      "      if (m.randomize()) ok++;\n"
      "      if (m.x == -1) neg++;\n"
      "      if (m.y == 200) two++;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d\", ok, neg, two);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8 8 8\n");
}

TEST(SoftConstraintPrioritiesRun,
     RelationsWithoutAPlainVariableSideResolveByPriority) {
  SimFixture f;
  std::string out = RunCapture(
      "class R;\n"
      "  rand int x, y;\n"
      "  constraint c { x inside {[0:9]}; y inside {[0:9]}; soft x < y + 1; "
      "soft x + y == 3; soft x == 2; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok = 0, hit = 0;\n"
      "  initial begin\n"
      "    static R r = new;\n"
      "    repeat (8) begin\n"
      "      if (r.randomize()) ok++;\n"
      "      if (r.x == 2 && r.y == 1) hit++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", ok, hit);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8 8\n");
}

TEST(SoftConstraintPrioritiesRun,
     RelationToAVariableWithRandModeOffKeepsItsSoftConstraints) {
  SimFixture f;
  std::string out = RunCapture(
      "class Q;\n"
      "  rand int x, y;\n"
      "  constraint c { x inside {[0:9]}; soft x < y; soft x > 3; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok = 0, hit = 0;\n"
      "  initial begin\n"
      "    static Q q = new;\n"
      "    q.y.rand_mode(0);\n"
      "    q.y = 5;\n"
      "    repeat (8) begin\n"
      "      if (q.randomize()) ok++;\n"
      "      if (q.x == 4 && q.y == 5) hit++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", ok, hit);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8 8\n");
}

}  // namespace
