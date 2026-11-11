#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(MemorySimulation,
     WordsOfRegLogicAndBitMemoriesAreWrittenAndReadByAddress) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  logic [7:0] mema [0:255];\n"
                 "  reg [7:0] memr [255:0];\n"
                 "  bit [7:0] memb [0:255];\n"
                 "  logic [7:0] data;\n"
                 "  int addr;\n"
                 "  initial begin\n"
                 "    addr = 5;\n"
                 "    $display(\"%h %h %h\", mema[7], memr[7], memb[7]);\n"
                 "    mema[5] = 0;\n"
                 "    memr[5] = 8'ha5;\n"
                 "    memb[5] = 8'h5a;\n"
                 "    data = mema[addr];\n"
                 "    $display(\"%h\", data);\n"
                 "    data = memr[addr];\n"
                 "    $display(\"%h\", data);\n"
                 "    data = memb[addr];\n"
                 "    $display(\"%h\", data);\n"
                 "    addr = 255;\n"
                 "    mema[addr] = 8'hff;\n"
                 "    memr[addr] = 8'h01;\n"
                 "    $display(\"%h %h %h\", mema[255], memr[255], "
                 "mema[254]);\n"
                 "    $display(\"%0d %0d %0d\", $size(mema), "
                 "$bits(mema[0]), $left(memr));\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "xx xx 00\n00\na5\n5a\nff 01 xx\n256 8 255\n");
}

TEST(MemorySimulation, MemoryWordsAreAddressedWhereverTheMemoryIsDeclared) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk;\n"
                       "  logic [7:0] pm [0:255];\n"
                       "endpackage\n"
                       "interface ifc;\n"
                       "  bit [7:0] im [0:255];\n"
                       "endinterface\n"
                       "class K;\n"
                       "  reg [7:0] km [0:255];\n"
                       "  static logic [7:0] sm [256];\n"
                       "endclass\n"
                       "module top;\n"
                       "  ifc ii();\n"
                       "  K k;\n"
                       "  int addr;\n"
                       "  if (1) begin : g\n"
                       "    logic [7:0] gm [0:255];\n"
                       "  end\n"
                       "  function automatic logic [7:0] f(int a);\n"
                       "    logic [7:0] fm [0:255];\n"
                       "    fm[a] = 8'h3c;\n"
                       "    return fm[a];\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    k = new;\n"
                       "    addr = 255;\n"
                       "    pk::pm[addr] = 8'h11;\n"
                       "    ii.im[addr] = 8'h22;\n"
                       "    k.km[addr] = 8'h33;\n"
                       "    K::sm[addr] = 8'h44;\n"
                       "    g.gm[addr] = 8'h55;\n"
                       "    $display(\"%h %h %h %h %h %h\", pk::pm[255], "
                       "ii.im[255], k.km[255], K::sm[255], g.gm[255], "
                       "f(addr));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "11 22 33 44 55 3c\n");
}

}  // namespace
