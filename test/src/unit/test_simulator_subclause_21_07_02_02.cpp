#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_vcd_dump_run.h"
#include "helpers_text_lines.h"

namespace delta {
namespace {

class VcdValueFormatE2E : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src) {
    return RunVcdDump(
        src, {.scope = "t",
              .registration = VcdSignalRegistration::kContextFiltered});
  }
};

std::string SimRegion(const std::string& content) {
  size_t pos = content.find("$enddefinitions");
  return pos == std::string::npos ? content : content.substr(pos);
}

TEST_F(VcdValueFormatE2E, ScalarFourStatesAbutIdentifierCode) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  initial begin\n"
      "    s = 1'b0;\n"
      "    $dumpvars;\n"
      "    #1 s = 1'b1;\n"
      "    #1 s = 1'bx;\n"
      "    #1 s = 1'bz;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "0!"));
  EXPECT_TRUE(HasLine(lines, "1!"));
  EXPECT_TRUE(HasLine(lines, "x!"));
  EXPECT_TRUE(HasLine(lines, "z!"));
  auto sim = SimRegion(content);
  EXPECT_EQ(sim.find("0 !"), std::string::npos);
  EXPECT_EQ(sim.find("1 !"), std::string::npos);
  for (const auto& l : lines) {
    EXPECT_TRUE(l.empty() || l[0] != 'b') << "scalar dumped as vector: " << l;
  }
}

TEST_F(VcdValueFormatE2E, VectorSingleDigitKeepsBaseLetterAndSpacing) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b0000;\n"
      "    $dumpvars;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "b0 !"));
  EXPECT_FALSE(HasLine(lines, "0!"));
  EXPECT_EQ(content.find("b 0"), std::string::npos);
}

TEST_F(VcdValueFormatE2E, ShortensOnlyRedundantFillDigits) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b1111;\n"
      "    $dumpvars;\n"
      "    #1 v = 4'b0010;\n"
      "    #1 v = 4'bxx10;\n"
      "    #1 v = 4'bzzx0;\n"
      "    #1 v = 4'b0x10;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "b1111 !"));
  EXPECT_TRUE(HasLine(lines, "b10 !"));
  EXPECT_TRUE(HasLine(lines, "bx10 !"));
  EXPECT_TRUE(HasLine(lines, "bzx0 !"));
  EXPECT_TRUE(HasLine(lines, "b0x10 !"));
  EXPECT_EQ(content.find("b0010"), std::string::npos);
  EXPECT_EQ(content.find("bxx10"), std::string::npos);
  EXPECT_EQ(content.find("bzzx0"), std::string::npos);
}

TEST_F(VcdValueFormatE2E, RightJustifiedRetainsLowOrderBits) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    v = 8'b00000110;\n"
      "    $dumpvars;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "b110 !"));
  EXPECT_FALSE(HasLine(lines, "b011 !"));
}

TEST_F(VcdValueFormatE2E, WideVectorShortensAcrossStorageWords) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [69:0] w;\n"
      "  initial begin\n"
      "    $dumpvars;\n"
      "    #1 w = 70'd5;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "bx !"));
  EXPECT_TRUE(HasLine(lines, "b101 !"));
  EXPECT_EQ(content.find("b0101"), std::string::npos);
}

TEST_F(VcdValueFormatE2E, RealRecordSpacingMatchesVectorRule) {
  auto content = RunVcd(
      "module t;\n"
      "  real r;\n"
      "  initial begin\n"
      "    r = 0.0;\n"
      "    $dumpvars;\n"
      "    #1 r = 0.5;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "r0 !"));
  EXPECT_TRUE(HasLine(lines, "r0.5 !"));
  EXPECT_EQ(content.find("r 0.5"), std::string::npos);
}

TEST_F(VcdValueFormatE2E, DeclarationInitializerValuesUseSameFormats) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s = 1'b1;\n"
      "  logic [3:0] v = 4'b0010;\n"
      "  initial $dumpvars;\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "1!"));
  EXPECT_TRUE(HasLine(lines, "b10 \""));
  EXPECT_EQ(SimRegion(content).find("b0010"), std::string::npos);
}

TEST_F(VcdValueFormatE2E, TwoStateVectorSharesVectorFormatAndShortening) {
  auto content = RunVcd(
      "module t;\n"
      "  bit [7:0] b;\n"
      "  initial begin\n"
      "    b = 8'b00000000;\n"
      "    $dumpvars;\n"
      "    #1 b = 8'b00001010;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "b0 !"));
  EXPECT_TRUE(HasLine(lines, "b1010 !"));
  EXPECT_EQ(SimRegion(content).find("b00001010"), std::string::npos);
}

TEST_F(VcdValueFormatE2E, IntegerVariableDumpsAsShortenedVector) {
  auto content = RunVcd(
      "module t;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    i = 0;\n"
      "    $dumpvars;\n"
      "    #1 i = 5;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "b0 !"));
  EXPECT_TRUE(HasLine(lines, "b101 !"));
  EXPECT_FALSE(HasLine(lines, "0!"));
}

TEST_F(VcdValueFormatE2E, NonblockingAssignmentProducesSameFormats) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    s = 1'b0;\n"
      "    v = 4'b0000;\n"
      "    $dumpvars;\n"
      "    #1 begin s <= 1'b1; v <= 4'b0010; end\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "1!"));
  EXPECT_TRUE(HasLine(lines, "b10 \""));
  auto sim = SimRegion(content);
  EXPECT_EQ(sim.find("1 !"), std::string::npos);
  EXPECT_EQ(sim.find("b0010"), std::string::npos);
}

TEST_F(VcdValueFormatE2E, EventTriggerDumpsScalarFormatMarker) {
  auto content = RunVcd(
      "module t;\n"
      "  event ev;\n"
      "  logic clk;\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    $dumpvars;\n"
      "    #5 -> ev;\n"
      "    #5 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_EQ(CountLine(lines, "1\""), 1u);
  size_t at_trigger = content.find("#5\n1\"");
  EXPECT_NE(at_trigger, std::string::npos);
  EXPECT_FALSE(HasLine(lines, "0\""));
  EXPECT_FALSE(HasLine(lines, "x\""));
  EXPECT_EQ(SimRegion(content).find("1 \""), std::string::npos);
}

}  // namespace
}  // namespace delta
