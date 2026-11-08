#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(InlineConstraintsRun, TheBlockResolvesInTheObjectThenTheCallersScope) {
  SimFixture f;
  std::string out = RunCapture(
      "class C1;\n"
      "  rand integer x;\n"
      "endclass\n"
      "class C2;\n"
      "  integer x;\n"
      "  integer y;\n"
      "  function int doit(C1 f, integer x, integer z);\n"
      "    return f.randomize() with { x < y + z; x >= y; };\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int success = 0, held = 0;\n"
      "  initial begin\n"
      "    static C1 f = new;\n"
      "    static C2 c2 = new;\n"
      "    c2.x = -1000;\n"
      "    c2.y = 10;\n"
      "    repeat (32) begin\n"
      "      if (c2.doit(f, -1000, 5) == 1) success++;\n"
      "      if (f.x >= 10 && f.x < 15) held++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", success, held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32\n");
}

TEST(InlineConstraintsRun, ARestrictedBlockResolvesOnlyTheListedNames) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand integer x;\n"
      "  rand integer y;\n"
      "endclass\n"
      "module t;\n"
      "  int success = 0, below = 0;\n"
      "  function int F(C obj, integer y);\n"
      "    F = obj.randomize() with (x) { x < y; };\n"
      "  endfunction\n"
      "  initial begin\n"
      "    static C obj = new;\n"
      "    repeat (32) begin\n"
      "      if (F(obj, 20) == 1) success++;\n"
      "      if (obj.x < 20) below++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", success, below);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32\n");
}

TEST(InlineConstraintsRun, AForeachIteratesAnArrayOfTheCallersScope) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  bit [3:0] banned[3] = '{1, 2, 3};\n"
      "  int bad = 0;\n"
      "  bit [5:0] seen = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (80) begin\n"
      "      if (c.randomize() with {\n"
      "            foreach (banned[i]) x != banned[i]; x < 6; } != 1) bad++;\n"
      "      if (c.x inside {1, 2, 3} || c.x >= 6) bad++;\n"
      "      else seen[c.x] = 1;\n"
      "    end\n"
      "    $display(\"%0d %0d\", bad, seen);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 49\n");
}

TEST(InlineConstraintsRun, AForeachIteratesAQueueOfTheCallersScope) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  bit [3:0] banned[$] = '{1, 2, 3};\n"
      "  int bad = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (40) begin\n"
      "      if (c.randomize() with {\n"
      "            foreach (banned[i]) x != banned[i]; x < 5; } != 1) bad++;\n"
      "      if (c.x inside {1, 2, 3} || c.x >= 5) bad++;\n"
      "    end\n"
      "    $display(\"%0d\", bad);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

TEST(InlineConstraintsRun, AForeachIteratesAMultidimensionalCallersArray) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  bit [3:0] banned [2][2] = '{'{1, 2}, '{3, 4}};\n"
      "  int bad = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (40) begin\n"
      "      if (c.randomize() with {\n"
      "            foreach (banned[i, j]) x != banned[i][j]; x < 6; } != 1)\n"
      "        bad++;\n"
      "      if (c.x inside {1, 2, 3, 4} || c.x >= 6) bad++;\n"
      "    end\n"
      "    $display(\"%0d\", bad);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

TEST(InlineConstraintsRun, ADottedNameResolvesItsHeadInTheObjectFirst) {
  SimFixture f;
  std::string out = RunCapture(
      "class Box;\n"
      "  bit [3:0] v;\n"
      "endclass\n"
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "  Box h = new;\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    static Box h = new;\n"
      "    c.h.v = 9;\n"
      "    h.v = 2;\n"
      "    repeat (4)\n"
      "      if (c.randomize() with { x == h.v; } == 1 && c.x == 9) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

TEST(InlineConstraintsRun, ARestrictedBlocksUnlistedHeadResolvesInTheCaller) {
  SimFixture f;
  std::string out = RunCapture(
      "class Box;\n"
      "  bit [3:0] v;\n"
      "endclass\n"
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "  Box h = new;\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    static Box h = new;\n"
      "    c.h.v = 9;\n"
      "    h.v = 2;\n"
      "    repeat (4)\n"
      "      if (c.randomize() with (x) { x == h.v; } == 1 && c.x == 2)\n"
      "        held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

TEST(InlineConstraintsRun, ACallWithNoArgumentListTakesItsClause) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    rand bit [3:0] x;\n"
      "  endclass\n"
      "  C obj = new;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    ok = obj.randomize with { x == 4'd7; };\n"
      "    $display(\"%0d %0d\", ok, obj.x);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 7\n");
}

}  // namespace
