#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

const char* const kGuardedHead =
    "class D;\n"
    "  int x;\n"
    "endclass\n"
    "class C;\n"
    "  rand int x, y;\n"
    "  D a, b;\n";

TEST(ConstraintGuardsRun, ANullHandleInTheGuardFailsRandomize) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kGuardedHead) +
          "  constraint c1 { (x < y || a.x > b.x || a.x == 5) -> x + y == 10; "
          "}\n"
          "endclass\n"
          "module t;\n"
          "  initial begin\n"
          "    static C o = new;\n"
          "    static D b = new;\n"
          "    o.b = b;\n"
          "    $display(\"%0d\", o.randomize());\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

TEST(ConstraintGuardsRun, ATrueDisjunctSiftsTheNullHandleAway) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kGuardedHead) +
          "  constraint c1 { (x < y || a.x > b.x || a.x == 5) -> x + y == 10; "
          "}\n"
          "endclass\n"
          "module t;\n"
          "  int ok = 0, sums = 0, apart = 0;\n"
          "  initial begin\n"
          "    static C o = new;\n"
          "    static D a = new;\n"
          "    a.x = 5;\n"
          "    o.a = a;\n"
          "    repeat (32) begin\n"
          "      if (o.randomize()) ok++;\n"
          "      if (o.x + o.y == 10) sums++;\n"
          "      if (o.x >= o.y) apart++;\n"
          "    end\n"
          "    $display(\"%0d %0d %0d\", ok, sums, apart > 0);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32 1\n");
}

TEST(ConstraintGuardsRun, AFalseConjunctEliminatesTheConstraint) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kGuardedHead) +
          "  constraint c1 { (x < y && a.x > b.x && a.x == 5) -> x + y == 10; "
          "}\n"
          "endclass\n"
          "module t;\n"
          "  int ok = 0, sums = 0;\n"
          "  initial begin\n"
          "    static C o = new;\n"
          "    static D a = new;\n"
          "    a.x = 6;\n"
          "    o.a = a;\n"
          "    repeat (32) begin\n"
          "      if (o.randomize()) ok++;\n"
          "      if (o.x + o.y == 10) sums++;\n"
          "    end\n"
          "    $display(\"%0d %0d\", ok, sums);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "32 0\n");
}

TEST(ConstraintGuardsRun, ARandomGuardGeneratesTheConditionalConstraint) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kGuardedHead) +
          "  constraint c1 { (x < y && a.x > b.x && a.x == 5) -> x + y == 10; "
          "}\n"
          "endclass\n"
          "module t;\n"
          "  int ok = 0, sums = 0;\n"
          "  initial begin\n"
          "    static C o = new;\n"
          "    static D a = new;\n"
          "    static D b = new;\n"
          "    a.x = 5;\n"
          "    b.x = 2;\n"
          "    o.a = a;\n"
          "    o.b = b;\n"
          "    repeat (32) begin\n"
          "      if (o.randomize() with { x < y; }) ok++;\n"
          "      if (o.x + o.y == 10) sums++;\n"
          "    end\n"
          "    $display(\"%0d %0d\", ok, sums);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32\n");
}

TEST(ConstraintGuardsRun, AnErrorNoOperandSiftsFailsRandomize) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kGuardedHead) +
          "  constraint c1 { (x < y && (a.x > b.x || a.x == 5)) -> x + y == "
          "10; }\n"
          "endclass\n"
          "module t;\n"
          "  initial begin\n"
          "    static C o = new;\n"
          "    static D a = new;\n"
          "    a.x = 8;\n"
          "    o.a = a;\n"
          "    $display(\"%0d\", o.randomize());\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

TEST(ConstraintGuardsRun, TheGuardedSortEliminatesTheTailsConstraint) {
  SimFixture f;
  std::string out = RunCapture(
      "class SList;\n"
      "  rand int n;\n"
      "  rand SList next;\n"
      "  constraint sort { if (next != null) n < next.n; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok = 0, ordered = 0, above = 0;\n"
      "  initial begin\n"
      "    static SList head = new;\n"
      "    static SList second = new;\n"
      "    static SList tail = new;\n"
      "    head.next = second;\n"
      "    second.next = tail;\n"
      "    repeat (32) begin\n"
      "      if (head.randomize()) ok++;\n"
      "      if (head.n < second.n && second.n < tail.n) ordered++;\n"
      "      if (tail.n > 0) above++;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d\", ok, ordered, above > 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32 1\n");
}

}  // namespace
