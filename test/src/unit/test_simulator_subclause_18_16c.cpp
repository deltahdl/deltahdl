#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunSrc(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

std::string RunAllTops(const std::string& src) {
  SimFixture f;
  return RunCaptureAllTops(src, f);
}

TEST(RandcaseCases, LowerNumbersSelectEarlierBranches) {
  EXPECT_EQ(RunSrc("module t;\n"
                   "  int unsigned r;\n"
                   "  int i, x, y, agree = 0;\n"
                   "  initial begin\n"
                   "    process p;\n"
                   "    p = process::self();\n"
                   "    for (i = 0; i < 64; i++) begin\n"
                   "      p.srandom(i);\n"
                   "      r = $urandom;\n"
                   "      p.srandom(i);\n"
                   "      randcase\n"
                   "        1 : x = 0;\n"
                   "        3 : x = 1;\n"
                   "      endcase\n"
                   "      p.srandom(i);\n"
                   "      randcase\n"
                   "        3 : y = 0;\n"
                   "        1 : y = 1;\n"
                   "      endcase\n"
                   "      if (x == (r % 4 < 1 ? 0 : 1) && y == (r % 4 < 3 ? 0 "
                   ": 1))\n"
                   "        agree++;\n"
                   "    end\n"
                   "    $display(\"%0d\", agree);\n"
                   "  end\n"
                   "endmodule\n"),
            "64\n");
}

TEST(RandcaseCases, OneExecutionTakesOneNumberFromTheThread) {
  EXPECT_EQ(RunSrc("module t;\n"
                   "  int unsigned a, b, z;\n"
                   "  int x;\n"
                   "  initial begin\n"
                   "    process p;\n"
                   "    p = process::self();\n"
                   "    p.srandom(5);\n"
                   "    randcase\n"
                   "      3 : x = 1;\n"
                   "      1 : x = 2;\n"
                   "      4 : x = 3;\n"
                   "    endcase\n"
                   "    a = $urandom;\n"
                   "    p.srandom(5);\n"
                   "    z = $urandom;\n"
                   "    b = $urandom;\n"
                   "    $display(\"%0d\", a == b);\n"
                   "  end\n"
                   "endmodule\n"),
            "1\n");
}

TEST(RandcaseCases, ANegativeByteWeightCountsAsItsUnsignedValue) {
  EXPECT_EQ(RunSrc("module t;\n"
                   "  byte w = -1;\n"
                   "  int i, first = 0;\n"
                   "  initial begin\n"
                   "    for (i = 0; i < 256; i++)\n"
                   "      randcase\n"
                   "        w : first++;\n"
                   "        32'd255 : ;\n"
                   "      endcase\n"
                   "    $display(\"%0d\", first > 64 && first < 192);\n"
                   "  end\n"
                   "endmodule\n"),
            "1\n");
}

TEST(RandcaseCases, DISABLED_TheSumIsTruncatedToTheWidestWeight) {
  EXPECT_EQ(RunSrc("module t;\n"
                   "  int i, first = 0;\n"
                   "  initial begin\n"
                   "    for (i = 0; i < 64; i++)\n"
                   "      randcase\n"
                   "        4'd12 : first++;\n"
                   "        4'd8 : ;\n"
                   "      endcase\n"
                   "    $display(\"%0d\", first);\n"
                   "  end\n"
                   "endmodule\n"),
            "64\n");
}

const char* const kPick =
    "randcase\n"
    "      0 : x = 1;\n"
    "      5 : x = 2;\n"
    "      0 : x = 3;\n"
    "    endcase\n";

TEST(RandcaseCases, ARandcaseInATaskSelects) {
  EXPECT_EQ(RunSrc(std::string("module t;\n"
                               "  int x;\n"
                               "  task automatic pick();\n"
                               "    ") +
                   kPick +
                   "  endtask\n"
                   "  initial begin\n"
                   "    pick();\n"
                   "    $display(\"%0d\", x);\n"
                   "  end\n"
                   "endmodule\n"),
            "2\n");
}

TEST(RandcaseCases, ARandcaseInAClassMethodReadsTheObjectsWeights) {
  EXPECT_EQ(RunSrc("class C;\n"
                   "  int w1 = 0, w2 = 7, w3 = 0;\n"
                   "  function int pick();\n"
                   "    int x;\n"
                   "    randcase\n"
                   "      w1 : x = 1;\n"
                   "      w2 : x = 2;\n"
                   "      w3 : x = 3;\n"
                   "    endcase\n"
                   "    return x;\n"
                   "  endfunction\n"
                   "endclass\n"
                   "module t;\n"
                   "  initial begin\n"
                   "    static C o = new;\n"
                   "    int a, b;\n"
                   "    a = o.pick();\n"
                   "    o.w2 = 0;\n"
                   "    o.w3 = 4;\n"
                   "    b = o.pick();\n"
                   "    $display(\"%0d %0d\", a, b);\n"
                   "  end\n"
                   "endmodule\n"),
            "2 3\n");
}

TEST(RandcaseCases, ARandcaseInAProgramSelects) {
  EXPECT_EQ(RunAllTops(std::string("program p;\n"
                                   "  int x;\n"
                                   "  initial begin\n"
                                   "    ") +
                       kPick +
                       "    $display(\"%0d\", x);\n"
                       "  end\n"
                       "endprogram\n"),
            "2\n");
}

TEST(RandcaseCases, ARandcaseInAPackageFunctionSelects) {
  EXPECT_EQ(RunSrc(std::string("package q;\n"
                               "  function automatic int pick();\n"
                               "    int x;\n"
                               "    ") +
                   kPick +
                   "    return x;\n"
                   "  endfunction\n"
                   "endpackage\n"
                   "module t;\n"
                   "  initial $display(\"%0d\", q::pick());\n"
                   "endmodule\n"),
            "2\n");
}

TEST(RandcaseCases, ARandcaseInAnInterfaceSelects) {
  EXPECT_EQ(RunSrc(std::string("interface ifc;\n"
                               "  int x;\n"
                               "  initial begin\n"
                               "    ") +
                   kPick +
                   "  end\n"
                   "endinterface\n"
                   "module t;\n"
                   "  ifc u();\n"
                   "  initial #1 $display(\"%0d\", u.x);\n"
                   "endmodule\n"),
            "2\n");
}

TEST(RandcaseCases, ARandcaseInAlwaysCombSelects) {
  EXPECT_EQ(RunSrc(std::string("module t;\n"
                               "  int x, k = 0;\n"
                               "  always_comb begin\n"
                               "    x = k;\n"
                               "    ") +
                   kPick +
                   "  end\n"
                   "  initial #1 $display(\"%0d\", x);\n"
                   "endmodule\n"),
            "2\n");
}

}  // namespace
