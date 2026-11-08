#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ProductionWeightsRun, TheWeightsSetTheProportionsAndAnAbsentOneIsOne) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int i, x, adds = 0, decs = 0, as = 0, bs = 0, every = 1;\n"
      "  int add_near, dec_near, a_near, b_near;\n"
      "  initial begin\n"
      "    for (i = 0; i < 5000; i++) begin\n"
      "      x = 0;\n"
      "      randsequence( main )\n"
      "        main  : first ;\n"
      "        first : add := 3 | dec := (1 + 1) ;\n"
      "        add   : { x = 1; } ;\n"
      "        dec   : { x = 2; } ;\n"
      "      endsequence\n"
      "      if (x == 1) adds++;\n"
      "      else if (x == 2) decs++;\n"
      "      else every = 0;\n"
      "    end\n"
      "    add_near = adds > 2850 && adds < 3150;\n"
      "    dec_near = decs > 1850 && decs < 2150;\n"
      "    for (i = 0; i < 4000; i++) begin\n"
      "      randsequence( main )\n"
      "        main : a | b := 3 ;\n"
      "        a    : { as++; } ;\n"
      "        b    : { bs++; } ;\n"
      "      endsequence\n"
      "    end\n"
      "    a_near = as > 900 && as < 1100;\n"
      "    b_near = bs > 2900 && bs < 3100;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", add_near, dec_near, every, "
      "a_near, b_near);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1 1 1\n");
}

TEST(ProductionWeightsRun, WeightsAreEvaluatedWhenTheProductionIsSelected) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int i, w, xs, p, picks[3], always_x, never_x, then_y;\n"
      "  initial begin\n"
      "    w = 10; xs = 0;\n"
      "    for (i = 0; i < 100; i++) begin\n"
      "      randsequence( main )\n"
      "        main : x_list := w | y_list := (10 - w) ;\n"
      "        x_list : { xs++; } ;\n"
      "        y_list : { } ;\n"
      "      endsequence\n"
      "    end\n"
      "    always_x = xs == 100;\n"
      "    w = 0; xs = 0;\n"
      "    for (i = 0; i < 100; i++) begin\n"
      "      randsequence( main )\n"
      "        main : x_list := w | y_list := (10 - w) ;\n"
      "        x_list : { xs++; } ;\n"
      "        y_list : { } ;\n"
      "      endsequence\n"
      "    end\n"
      "    never_x = xs == 0;\n"
      "    w = 10; p = 0;\n"
      "    randsequence( main )\n"
      "      main : pick pick pick ;\n"
      "      pick : x_list := w | y_list := (10 - w) ;\n"
      "      x_list : { picks[p] = 1; p++; w = 0; } ;\n"
      "      y_list : { picks[p] = 2; p++; } ;\n"
      "    endsequence\n"
      "    then_y = picks[0] == 1 && picks[1] == 2 && picks[2] == 2;\n"
      "    $display(\"%0d %0d %0d\", always_x, never_x, then_y);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1\n");
}

TEST(ProductionWeightsRun, AParameterWeighsAndALoneListIsGeneratedWhatever) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  parameter int W3 = 3;\n"
      "  int i, adds = 0, lone = 0, add_near;\n"
      "  initial begin\n"
      "    for (i = 0; i < 5000; i++) begin\n"
      "      randsequence( first )\n"
      "        first : add := W3 | dec := 2 ;\n"
      "        add   : { adds++; } ;\n"
      "        dec   : { } ;\n"
      "      endsequence\n"
      "    end\n"
      "    add_near = adds > 2850 && adds < 3150;\n"
      "    randsequence( main )\n"
      "      main : only := 0 ;\n"
      "      only : { lone = 1; } ;\n"
      "    endsequence\n"
      "    $display(\"%0d %0d\", add_near, lone);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1\n");
}

}  // namespace
