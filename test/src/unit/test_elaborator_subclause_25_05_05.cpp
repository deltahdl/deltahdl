#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClockingModportElaboration, SingleClockingPortAccepted) {
  EXPECT_TRUE(
      ElabOk("interface ifc(input logic clk);\n"
             "  clocking cb @(posedge clk); endclocking\n"
             "  modport mp(clocking cb);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClockingModportElaboration, ClockingFromDifferentInterfaceErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface other(input logic clk);\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "endinterface\n"
      "interface ifc(input logic clk);\n"
      "  modport mp(clocking cb);\n"
      "endinterface\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "clocking identifier 'cb' in modport 'mp' is not declared in interface "
      "'ifc'",
      5, "25.5.5"));
}

TEST(ClockingModportElaboration, ClockingNamingNonClockingItemErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc(input logic clk);\n"
      "  logic cb;\n"
      "  modport mp(clocking cb);\n"
      "endinterface\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "clocking identifier 'cb' in modport 'mp' is not declared in interface "
      "'ifc'",
      3, "25.5.5"));
}

TEST(ClockingModportElaboration, ClockingBlockWithSignalsThroughInterfacePort) {
  EXPECT_TRUE(
      ElabOk("interface bus(input logic clk);\n"
             "  logic req, gnt;\n"
             "  clocking cb @(posedge clk);\n"
             "    input gnt;\n"
             "    output req;\n"
             "  endclocking\n"
             "  modport tb(clocking cb);\n"
             "endinterface\n"
             "module dev(bus.tb b);\n"
             "endmodule\n"
             "module top;\n"
             "  logic clk;\n"
             "  bus b(clk);\n"
             "  dev d(b);\n"
             "endmodule\n"));
}

TEST(ClockingModportElaboration,
     AClockingBlockAModportOmitsIsReportedOnceThroughAVirtualInterface) {
  ElabFixture f;
  ElaborateSrc(
      "interface A_Bus(input logic clk);\n"
      "  logic req;\n"
      "  clocking sb @(posedge clk);\n"
      "    output req;\n"
      "  endclocking\n"
      "  modport STB(clocking sb);\n"
      "  modport TB(input req);\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  A_Bus b(clk);\n"
      "  virtual A_Bus.TB v = b;\n"
      "  initial v.sb.req <= 1;\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "clocking block 'sb' is not accessible through "
                            "modport 'TB' of interface 'A_Bus'",
                            13, "25.5.5"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "'sb' is not a clocking block or member of "
                             "interface 'A_Bus'",
                             13, "25.9"));
}

TEST(ClockingModportElaboration,
     AClockingBlockOfAnEnclosingInterfaceIsRefused) {
  ElabFixture f;
  ElaborateSrc(
      "interface outer(input logic clk);\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "  interface n;\n"
      "    modport mp(clocking cb);\n"
      "  endinterface\n"
      "  interface k;\n"
      "    logic clk2;\n"
      "    clocking kb @(posedge clk2); endclocking\n"
      "    modport mp(clocking kb);\n"
      "  endinterface\n"
      "  n ni();\n"
      "  k ki();\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk;\n"
      "  outer o(clk);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "clocking identifier 'cb' in modport 'mp' is not declared in interface "
      "'n'",
      4, "25.5.5"));
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "clocking identifier 'kb' in modport 'mp' is not declared in interface "
      "'k'",
      9, "25.5.5"));
}

TEST(ClockingModportElaboration, AClockingBlockOfANestedInterfaceIsRefused) {
  ElabFixture f;
  ElaborateSrc(
      "interface outer(input logic clk);\n"
      "  interface n;\n"
      "    clocking nb @(posedge clk); endclocking\n"
      "  endinterface\n"
      "  n ni();\n"
      "  modport mp(clocking nb);\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk;\n"
      "  outer o(clk);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "clocking identifier 'nb' in modport 'mp' is not declared in interface "
      "'outer'",
      6, "25.5.5"));
}

constexpr const char* kSynchronousAndAsynchronousBus =
    "interface A_Bus(input logic clk);\n"
    "  logic req;\n"
    "  clocking sb @(posedge clk);\n"
    "    output req;\n"
    "  endclocking\n"
    "  modport STB(clocking sb);\n"
    "  modport TB(output req);\n"
    "endinterface\n";

std::string BusProgram(const std::string& body) {
  return std::string(kSynchronousAndAsynchronousBus) +
         "program T(A_Bus.STB s, A_Bus.TB a);\n"
         "  initial begin\n" +
         body +
         "  end\n"
         "endprogram\n"
         "module top;\n"
         "  logic clk = 0;\n"
         "  A_Bus b1(clk), b2(clk);\n"
         "  T t(b1, b2);\n"
         "endmodule\n";
}

TEST(ClockingModportElaboration, AClockingModportHidesTheSignalsOfItsBlock) {
  ElabFixture f;
  ElaborateSrc(BusProgram("    s.sb.req <= 1;\n"
                          "    s.req = 1;\n"),
               f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'req' is not accessible through modport 'STB' of interface 'A_Bus'", 12,
      "25.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(ClockingModportElaboration,
     AClockingBlockAModportOmitsIsRefusedThroughAPort) {
  ElabFixture f;
  ElaborateSrc(BusProgram("    a.req = 1;\n"
                          "    a.sb.req <= 1;\n"),
               f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "clocking block 'sb' is not accessible through "
                            "modport 'TB' of interface 'A_Bus'",
                            12, "25.5.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(ClockingModportElaboration,
     ASynchronousAndAnAsynchronousModportPortAreAccepted) {
  ElabFixture f;
  ElaborateSrc(BusProgram("    s.sb.req <= 1;\n"
                          "    a.req = 1;\n"),
               f, "top");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
