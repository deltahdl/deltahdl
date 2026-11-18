#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string SyncBus(const std::string& storage) {
  return "interface SyncBus(input logic clk);\n"
         "  " +
         storage +
         " a, b, c;\n"
         "  clocking sb @(posedge clk);\n"
         "    input a; output b; inout c;\n"
         "  endclocking\n"
         "endinterface\n"
         "typedef virtual SyncBus VI;\n";
}

std::string RunThroughName(const std::string& storage,
                           const std::string& declaration,
                           const std::string& binding,
                           const std::string& name) {
  SimFixture f;
  std::string out =
      RunCapture(SyncBus(storage) + "class Holder; " + declaration +
                     " endclass\n"
                     "module top;\n"
                     "  logic clk = 0;\n"
                     "  initial repeat (12) #5 clk = ~clk;\n"
                     "  SyncBus b1(clk);\n"
                     "  logic ad = 0;\n"
                     "  assign b1.a = ad;\n"
                     "  " +
                     declaration +
                     "\n"
                     "  Holder h = new;\n"
                     "  initial begin\n"
                     "    " +
                     binding +
                     "\n"
                     "    #6 ad = 1;\n"
                     "    @(" +
                     name +
                     ".sb);\n"
                     "    $display(\"event at %0t a=%0d b=%b\", $time, " +
                     name +
                     ".sb.a, b1.b);\n"
                     "    " +
                     name +
                     ".sb.b <= 0;\n"
                     "    #1 $display(\"b=%b at %0t\", b1.b, $time);\n"
                     "    @(" +
                     name +
                     ".sb);\n"
                     "    " +
                     name +
                     ".sb.c <= ##1 1;\n"
                     "    #1 $display(\"c=%b at %0t\", b1.c, $time);\n"
                     "    @(" +
                     name +
                     ".sb);\n"
                     "    #1 $display(\"c=%b at %0t\", b1.c, $time);\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

constexpr const char* kOnNets =
    "event at 15 a=1 b=z\nb=0 at 16\nc=z at 26\nc=1 at 36\n";
constexpr const char* kOnVariables =
    "event at 15 a=1 b=x\nb=0 at 16\nc=x at 26\nc=1 at 36\n";

TEST(VirtualInterfaceClockingSim, AVariableSamplesAndDrivesNets) {
  EXPECT_EQ(RunThroughName("wire", "virtual SyncBus v;", "v = b1;", "v"),
            kOnNets);
}

TEST(VirtualInterfaceClockingSim, AVariableSamplesAndDrivesVariables) {
  EXPECT_EQ(RunThroughName("logic", "virtual SyncBus v;", "v = b1;", "v"),
            kOnVariables);
}

TEST(VirtualInterfaceClockingSim, AnArrayElementSamplesAndDrivesNets) {
  EXPECT_EQ(
      RunThroughName("wire", "virtual SyncBus v[2];", "v[1] = b1;", "v[1]"),
      kOnNets);
}

TEST(VirtualInterfaceClockingSim, AnArrayElementSamplesAndDrivesVariables) {
  EXPECT_EQ(
      RunThroughName("logic", "virtual SyncBus v[2];", "v[1] = b1;", "v[1]"),
      kOnVariables);
}

TEST(VirtualInterfaceClockingSim, AClassPropertySamplesAndDrivesNets) {
  EXPECT_EQ(RunThroughName("wire", "virtual SyncBus v;", "h.v = b1;", "h.v"),
            kOnNets);
}

TEST(VirtualInterfaceClockingSim, AClassPropertySamplesAndDrivesVariables) {
  EXPECT_EQ(RunThroughName("logic", "virtual SyncBus v;", "h.v = b1;", "h.v"),
            kOnVariables);
}

TEST(VirtualInterfaceClockingSim, DISABLED_ATypedefVariableSamplesAndDrives) {
  EXPECT_EQ(RunThroughName("wire", "VI v;", "v = b1;", "v"), kOnNets);
}

TEST(VirtualInterfaceClockingSim,
     DISABLED_ATypedefArrayElementSamplesAndDrives) {
  EXPECT_EQ(RunThroughName("logic", "VI v[2];", "v[1] = b1;", "v[1]"),
            kOnVariables);
}

TEST(VirtualInterfaceClockingSim,
     DISABLED_ATypedefClassPropertySamplesAndDrives) {
  EXPECT_EQ(RunThroughName("wire", "VI v;", "h.v = b1;", "h.v"), kOnNets);
}

std::string RunTheSectionsTask(const std::string& storage) {
  SimFixture f;
  std::string out = RunCapture(
      SyncBus(storage) +
          "task do_it(VI v);\n"
          "  if (v.sb.a == 1)\n"
          "    v.sb.b <= 0;\n"
          "  else\n"
          "    v.sb.c <= ##1 1;\n"
          "endtask\n"
          "module top;\n"
          "  logic clk = 0;\n"
          "  initial repeat (16) #5 clk = ~clk;\n"
          "  SyncBus b1(clk);\n"
          "  SyncBus b2(clk);\n"
          "  logic a1 = 1, a2 = 0;\n"
          "  assign b1.a = a1;\n"
          "  assign b2.a = a2;\n"
          "  initial begin\n"
          "    automatic VI v[2] = '{b1, b2};\n"
          "    @(b1.sb);\n"
          "    do_it(v[0]);\n"
          "    do_it(v[1]);\n"
          "    repeat (3) begin\n"
          "      #1 $display(\"%0t b1 %b%b b2 %b%b\", $time, b1.b, b1.c, "
          "b2.b, b2.c);\n"
          "      @(b1.sb);\n"
          "    end\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

TEST(VirtualInterfaceClockingSim, TheSectionsTaskHandlesABusOfNets) {
  EXPECT_EQ(RunTheSectionsTask("wire"),
            "6 b1 0z b2 zz\n16 b1 0z b2 z1\n26 b1 0z b2 z1\n");
}

TEST(VirtualInterfaceClockingSim,
     TheSectionsTaskHandlesABusOfVariablesUnchanged) {
  EXPECT_EQ(RunTheSectionsTask("logic"),
            "6 b1 0x b2 xx\n16 b1 0x b2 x1\n26 b1 0x b2 x1\n");
}

}  // namespace
