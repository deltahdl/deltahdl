#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"

TEST(UnconnectedDriveSimulation, Pull1ModuleSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`unconnected_drive pull1\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd10;\n"
      "endmodule\n"
      "`nounconnected_drive\n",
      "result", CuPropagation::kUnconnectedDrive);
  EXPECT_EQ(result, 10u);
}

TEST(UnconnectedDriveSimulation, Pull1DrivesUnconnectedInputHighAtRuntime) {
  auto result = PreprocessAndGet(
      "`unconnected_drive pull1\n"
      "module child(input wire a, output logic [7:0] b);\n"
      "  assign b = a ? 8'd1 : 8'd0;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result));\n"
      "endmodule\n",
      "result", CuPropagation::kUnconnectedDrive);
  EXPECT_EQ(result, 1u);
}

TEST(UnconnectedDriveSimulation, Pull0DrivesUnconnectedInputLowAtRuntime) {
  auto result = PreprocessAndGet(
      "`unconnected_drive pull0\n"
      "module child(input wire a, output logic [7:0] b);\n"
      "  assign b = a ? 8'd0 : 8'd1;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result));\n"
      "endmodule\n",
      "result", CuPropagation::kUnconnectedDrive);
  EXPECT_EQ(result, 1u);
}

static std::string PassThrough(const std::string& name) {
  return "module " + name +
         "(input logic a, output logic b);\n"
         "  assign b = a;\n"
         "endmodule\n";
}

TEST(UnconnectedDriveSimulation, ATrailingDirectiveLeavesTheModulesBeforeIt) {
  SimFixture f;
  EXPECT_EQ(
      PreprocessAndCapture("`unconnected_drive pull1\n" + PassThrough("sub") +
                               "module t;\n"
                               "  logic b;\n"
                               "  sub s(.b(b));\n"
                               "  initial #1 $display(\"%b\", b);\n"
                               "endmodule\n"
                               "`unconnected_drive pull0\n",
                           f),
      "1\n");
}

TEST(UnconnectedDriveSimulation, EachChildTakesTheDriveAtItsDefinition) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture(
                "`unconnected_drive pull1\n" + PassThrough("sub1") +
                    "`nounconnected_drive\n" + PassThrough("sub2") +
                    "`unconnected_drive pull0\n" + PassThrough("sub3") +
                    "`nounconnected_drive\n"
                    "module t;\n"
                    "  logic x, y, z;\n"
                    "  sub1 s1(.b(x));\n"
                    "  sub2 s2(.b(y));\n"
                    "  sub3 s3(.b(z));\n"
                    "  initial #1 $display(\"%b %b %b\", "
                    "x, y, z);\n"
                    "endmodule\n",
                f),
            "1 z 0\n");
}

static std::string RunDrive(const std::string& src) {
  SimFixture f;
  return PreprocessAndCapture(src, f);
}

static std::string Pulled(const char* drive, const std::string& child,
                          const std::string& top_items,
                          const std::string& shown) {
  return std::string("`unconnected_drive ") + drive + "\n" + child +
         "`nounconnected_drive\nmodule t;\n" + top_items +
         "  initial #1 $display(" + shown + ");\nendmodule\n";
}

TEST(UnconnectedDriveSimulation, DISABLED_EveryBitOfAVectorInputIsPulled) {
  const std::string kChild = "module s(input wire [3:0] a);\nendmodule\n";
  EXPECT_EQ(RunDrive(Pulled("pull1", kChild, "  s u();\n", "\"%b\", u.a")),
            "1111\n");
  EXPECT_EQ(RunDrive(Pulled("pull0", kChild, "  s u();\n", "\"%b\", u.a")),
            "0000\n");
}

TEST(UnconnectedDriveSimulation, AVariableInputIsPulled) {
  const std::string kChild = "module s(input var logic v);\nendmodule\n";
  EXPECT_EQ(RunDrive(Pulled("pull1", kChild, "  s u();\n", "\"%b\", u.v")),
            "1\n");
  EXPECT_EQ(RunDrive(Pulled("pull0", kChild, "  s u();\n", "\"%b\", u.v")),
            "0\n");
}

TEST(UnconnectedDriveSimulation, AProgramInputIsPulled) {
  const std::string kChild =
      "program p(input wire a);\n  initial #1 $display(\"%b\", a);\n"
      "endprogram\n";
  for (const char* drive : {"pull1", "pull0"}) {
    std::string src = std::string("`unconnected_drive ") + drive + "\n" +
                      kChild +
                      "`nounconnected_drive\nmodule t;\n  p u();\n"
                      "endmodule\n";
    EXPECT_EQ(RunDrive(src), drive[4] == '1' ? "1\n" : "0\n") << drive;
  }
}

TEST(UnconnectedDriveSimulation, AnInterfaceInputIsPulled) {
  const std::string kChild = "interface i(input wire a);\nendinterface\n";
  EXPECT_EQ(RunDrive(Pulled("pull1", kChild, "  i u();\n", "\"%b\", u.a")),
            "1\n");
  EXPECT_EQ(RunDrive(Pulled("pull0", kChild, "  i u();\n", "\"%b\", u.a")),
            "0\n");
}

TEST(UnconnectedDriveSimulation, EmptyNamedAndBlankOrderedConnectionsPull) {
  EXPECT_EQ(RunDrive(Pulled("pull1", "module s(input wire a);\nendmodule\n",
                            "  s u(.a());\n", "\"%b\", u.a")),
            "1\n");
  EXPECT_EQ(RunDrive(Pulled("pull1",
                            "module s(input wire a, input wire b);\n"
                            "endmodule\n",
                            "  wire y = 0;\n  s u(, y);\n", "\"%b\", u.a")),
            "1\n");
}

TEST(UnconnectedDriveSimulation, OutputAndInoutPortsAreNotPulled) {
  EXPECT_EQ(RunDrive(Pulled("pull1",
                            "module s(output wire o, inout wire io);\n"
                            "endmodule\n",
                            "  s u();\n", "\"%b%b\", u.o, u.io")),
            "zz\n");
}

TEST(UnconnectedDriveSimulation, DISABLED_ThePulledValueHasPullStrength) {
  const std::string kChild = "module s(input wire a);\nendmodule\n";
  EXPECT_EQ(RunDrive(Pulled("pull1", kChild, "  s u();\n", "\"%v\", u.a")),
            "Pu1\n");
  EXPECT_EQ(RunDrive(Pulled("pull0", kChild, "  s u();\n", "\"%v\", u.a")),
            "Pu0\n");
}

TEST(UnconnectedDriveSimulation,
     ProgramAndInterfaceTakeTheirOwnDefinitionsDrive) {
  EXPECT_EQ(RunDrive("`unconnected_drive pull1\n"
                     "program p(input wire a);\n"
                     "  initial #1 $display(\"p %b\", a);\nendprogram\n"
                     "interface i(input wire a);\nendinterface\n"
                     "`unconnected_drive pull0\n"
                     "module t;\n  p pu();\n  i iu();\n"
                     "  initial #1 $display(\"i %b\", iu.a);\nendmodule\n"),
            "i 1\np 1\n");
}
