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

}  // namespace
