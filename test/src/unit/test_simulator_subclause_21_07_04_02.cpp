#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_vcd_dump_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

class ExtendedVcdNodeInfoSim : public VcdDumpRunTestBase {
 protected:
  std::string RunPortVcd(const std::string& src) {
    return RunVcdDump(src,
                      {.scope = "t",
                       .registration = VcdSignalRegistration::kContextFiltered,
                       .extended = true});
  }
};

Logic4Vec MakeBits(Arena& arena, uint32_t width, uint64_t val) {
  return MakeLogic4VecVal(arena, width, val);
}

TEST_F(ExtendedVcdNodeInfoSim, MatchesNodeInformationExample) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.SetExtendedPortNodes();
    vcd.WriteHeader("1ns");
    vcd.BeginScope("testbench.DUT");
    auto* count_out = arena_.Create<Variable>();
    count_out->value = MakeBits(arena_, 1, 0);
    vcd.RegisterSignal("count_out", 1, count_out);
    auto* carry = arena_.Create<Variable>();
    carry->value = MakeBits(arena_, 1, 0);
    vcd.RegisterSignal("carry", 1, carry);
    auto* data = arena_.Create<Variable>();
    data->value = MakeBits(arena_, 4, 0);
    vcd.RegisterSignal(VcdSignalSpec{"data", 4, data, NetType::kWire, 0, 3});
    auto* reset = arena_.Create<Variable>();
    reset->value = MakeBits(arena_, 1, 0);
    vcd.RegisterSignal("reset", 1, reset);
    vcd.EndScope();
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$var port 1 <0 count_out $end"), std::string::npos);
  EXPECT_NE(content.find("$var port 1 <1 carry $end"), std::string::npos);
  EXPECT_NE(content.find("$var port [0:3] <2 data $end"), std::string::npos);
  EXPECT_NE(content.find("$var port 1 <3 reset $end"), std::string::npos);
  EXPECT_EQ(content.find("$var wire"), std::string::npos);
}

TEST_F(ExtendedVcdNodeInfoSim, BusIndexRangePreservesDeclaredMsbLsbOrder) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.SetExtendedPortNodes();
    vcd.WriteHeader("1ns");
    auto* data = arena_.Create<Variable>();
    data->value = MakeBits(arena_, 8, 0);
    vcd.RegisterSignal(VcdSignalSpec{"data", 8, data, NetType::kWire, 7, 0});
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$var port [7:0] <0 data $end"), std::string::npos);
  EXPECT_EQ(content.find("[0:7]"), std::string::npos);
}

TEST_F(ExtendedVcdNodeInfoSim,
       BusPrintsIndexRangeScalarPrintsOneFromDeclaration) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic [3:0] data = 4'b0000;\n"
      "  logic en = 1'b0;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_NE(content.find("$var port [3:0] <0 data $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("$var port 1 <1 en $end"), std::string::npos)
      << content;
  EXPECT_EQ(content.find("$var port 4 "), std::string::npos) << content;
  EXPECT_EQ(content.find("$var wire"), std::string::npos);
  EXPECT_EQ(content.find("$var logic"), std::string::npos);
}

TEST_F(ExtendedVcdNodeInfoSim, VarTypeIsPortForEveryDeclaredKind) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  integer i = 0;\n"
      "  real r = 0.0;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_NE(content.find("$var port 1 <0 a $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("$var port [31:0] <1 i $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("$var port 1 <2 r $end"), std::string::npos)
      << content;
  EXPECT_EQ(content.find("$var integer"), std::string::npos);
  EXPECT_EQ(content.find("$var real"), std::string::npos);
  EXPECT_EQ(content.find("$var logic"), std::string::npos);
}

TEST_F(ExtendedVcdNodeInfoSim, IdentifierCodesAreAscendingIntegersFromZero) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  logic b = 1'b0;\n"
      "  logic c = 1'b0;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_NE(content.find("$var port 1 <0 a $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("$var port 1 <1 b $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("$var port 1 <2 c $end"), std::string::npos)
      << content;
  EXPECT_EQ(content.find("$var port 1 <! "), std::string::npos) << content;
}

TEST_F(ExtendedVcdNodeInfoSim,
       PortDeclarationRangeSelectsBusSizeScalarPortSelectsOne) {
  auto content = RunPortVcd(
      "module t(input [3:0] data, input en);\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_NE(content.find("$var port [3:0] <0 data $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("$var port 1 <1 en $end"), std::string::npos)
      << content;
  EXPECT_EQ(content.find("$var port 4 "), std::string::npos) << content;
}

TEST_F(ExtendedVcdNodeInfoSim, NetPortUsesPortKeywordWithItsIndexRange) {
  auto content = RunPortVcd(
      "module t(output wire [7:0] bus, input en);\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_NE(content.find("$var port [7:0] <0 bus $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("$var port 1 <1 en $end"), std::string::npos)
      << content;
  EXPECT_EQ(content.find("$var wire"), std::string::npos) << content;
}

}  // namespace
}  // namespace delta
