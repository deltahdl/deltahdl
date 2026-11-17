#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(CrossAutomaticTypesSim,
     DISABLED_CrossValTypeTakesEachCoverpointsNameAndType) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  bit [3:0] p; logic [0:2] q; logic [7:0] x; logic [3:0] y;\n"
          "  bit v;\n"
          "  covergroup cg;\n"
          "    cp: coverpoint p { bins b[] = {[0:15]}; }\n"
          "    cq: coverpoint q;\n"
          "    cc: coverpoint {x, y};\n"
          "    X: cross cp, cq, cc, v {\n"
          "      function CrossQueueType mk();\n"
          "        CrossValType e;\n"
          "        $display(\"%0d %0d %0d %0d %0d\", $bits(CrossValType),\n"
          "                 $bits(e.cp), $bits(e.cq), $bits(e.cc), "
          "$bits(e.v));\n"
          "        for (int i = 0; i < 40; i++) begin\n"
          "          e.cp = i; e.cq = 5; e.cc = 12'hABC; e.v = 1;\n"
          "          mk.push_back(e);\n"
          "        end\n"
          "        $display(\"%0d %0d %0d %h\", mk.size(), mk[39].cp,\n"
          "                 mk[39].cq, mk[39].cc);\n"
          "      endfunction\n"
          "      bins s = mk();\n"
          "    }\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "endmodule\n",
          f),
      "20 4 3 12 1\n40 7 5 abc\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
