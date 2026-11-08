#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Design(const std::string& body) {
  return "class Bus;\n"
         "  rand bit [15:0] addr;\n"
         "  rand bit [31:0] data;\n"
         "  constraint word_align { addr[1:0] == 2'b0; }\n"
         "endclass\n"
         "typedef enum {low, mid, high} AddrType;\n"
         "class MyBus extends Bus;\n"
         "  rand AddrType atype;\n"
         "  constraint addr_range {\n"
         "    (atype == low) -> addr inside { [0 : 15] };\n"
         "    (atype == mid) -> addr inside { [16 : 127] };\n"
         "    (atype == high) -> addr inside { [128 : 255] };\n"
         "  }\n"
         "endclass\n"
         "class PowerOfTwo;\n"
         "  rand bit [4:0] n;\n"
         "  rand bit [31:0] d;\n"
         "  constraint shifted { d == 1 << n; }\n"
         "endclass\n"
         "module t;\n"
         "  function bit in_range(MyBus b);\n"
         "    case (b.atype)\n"
         "      low: in_range = b.addr <= 15;\n"
         "      mid: in_range = b.addr >= 16 && b.addr <= 127;\n"
         "      high: in_range = b.addr >= 128 && b.addr <= 255;\n"
         "      default: in_range = 0;\n"
         "    endcase\n"
         "  endfunction\n"
         "  initial begin\n"
         "    static Bus bus = new;\n"
         "    static MyBus mybus = new;\n"
         "    static PowerOfTwo p2 = new;\n"
         "    static int ok = 0, aligned = 0, ranged = 0, met = 0;\n" +
         body +
         "  end\n"
         "endmodule\n";
}

TEST(ConstrainedRandomConcepts, TheObjectAndItsExtensionMeetAllConstraints) {
  SimFixture f;
  std::string out = RunCapture(
      Design("    repeat (50) begin\n"
             "      if (bus.randomize() == 1) ok++;\n"
             "      if (bus.addr[1:0] == 2'b0) aligned++;\n"
             "    end\n"
             "    $display(\"%0d %0d\", ok, aligned);\n"
             "    ok = 0; aligned = 0;\n"
             "    repeat (30) begin\n"
             "      if (mybus.randomize() == 1) ok++;\n"
             "      if (mybus.addr[1:0] == 2'b0) aligned++;\n"
             "      if (in_range(mybus)) ranged++;\n"
             "    end\n"
             "    $display(\"%0d %0d %0d\", ok, aligned, ranged);\n"),
      f);
  EXPECT_EQ(out, "50 50\n30 30 30\n");
}

TEST(ConstrainedRandomConcepts, InLineConstraintsAndAlgebraAreSolved) {
  SimFixture f;
  std::string out = RunCapture(
      Design("    ok = mybus.randomize() with {atype == low;};\n"
             "    met += ok && mybus.atype == low && mybus.addr <= 15 && "
             "mybus.addr[1:0] == 0;\n"
             "    ok = mybus.randomize() with {10 <= addr && addr <= 20;};\n"
             "    met += ok && mybus.addr >= 10 && mybus.addr <= 20 && "
             "mybus.addr[1:0] == 0;\n"
             "    ok = mybus.randomize() with {(data & (data - 1)) == 0;};\n"
             "    met += ok && (mybus.data & (mybus.data - 1)) == 0;\n"
             "    ok = 0;\n"
             "    repeat (10) if (p2.randomize() == 1 && p2.d == (1 << p2.n)) "
             "ok++;\n"
             "    $display(\"%0d %0d\", met, ok);\n"),
      f);
  EXPECT_EQ(out, "3 10\n");
}

TEST(ConstrainedRandomConcepts, TheExerciseBusTaskMeetsItsConstraints) {
  SimFixture f;
  std::string out = RunCapture(
      "class Bus;\n"
      "  rand bit [15:0] addr;\n"
      "  rand bit [31:0] data;\n"
      "  constraint word_align { addr[1:0] == 2'b0; }\n"
      "endclass\n"
      "typedef enum {low, mid, high} AddrType;\n"
      "class MyBus extends Bus;\n"
      "  rand AddrType atype;\n"
      "  constraint addr_range {\n"
      "    (atype == low) -> addr inside { [0 : 15] };\n"
      "    (atype == mid) -> addr inside { [16 : 127] };\n"
      "    (atype == high) -> addr inside { [128 : 255] };\n"
      "  }\n"
      "endclass\n"
      "module t;\n"
      "  task exercise_bus(MyBus bus, output int met);\n"
      "    int res;\n"
      "    met = 0;\n"
      "    res = bus.randomize() with {atype == low;};\n"
      "    $display(\"%0d %0d %0d %0d\", res, bus.atype == low, "
      "bus.addr <= 15, bus.addr[1:0] == 0);\n"
      "    met += res && bus.atype == low && bus.addr <= 15 && "
      "bus.addr[1:0] == 0;\n"
      "    res = bus.randomize() with {10 <= addr && addr <= 20;};\n"
      "    $display(\"%0d %0d %0d\", res, bus.addr >= 10 && bus.addr <= 20, "
      "bus.addr[1:0] == 0);\n"
      "    met += res && bus.addr >= 10 && bus.addr <= 20 && "
      "bus.addr[1:0] == 0;\n"
      "    res = bus.randomize() with {(data & (data - 1)) == 0;};\n"
      "    $display(\"%0d %0d\", res, (bus.data & (bus.data - 1)) == 0);\n"
      "    met += res && (bus.data & (bus.data - 1)) == 0;\n"
      "  endtask\n"
      "  initial begin\n"
      "    static MyBus mybus = new;\n"
      "    int met;\n"
      "    exercise_bus(mybus, met);\n"
      "    $display(\"met %0d\", met);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1 1\n1 1 1\n1 1\nmet 3\n");
}

TEST(ConstrainedRandomConcepts, ConstraintModeDisablesANamedBlock) {
  SimFixture f;
  std::string out = RunCapture(
      Design("    mybus.word_align.constraint_mode(0);\n"
             "    ok = mybus.randomize() with {addr[0] || addr[1];};\n"
             "    $display(\"%0d %0d\", ok, mybus.addr[1:0] != 0);\n"
             "    mybus.word_align.constraint_mode(1);\n"
             "    ok = mybus.randomize();\n"
             "    $display(\"%0d %0d\", ok, mybus.addr[1:0] == 0);\n"),
      f);
  EXPECT_EQ(out, "1 1\n1 1\n");
}

}  // namespace
