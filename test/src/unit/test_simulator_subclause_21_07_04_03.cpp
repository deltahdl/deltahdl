#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/types.h"
#include "fixture_vcd_dump_from_source.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_text_lines.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

class ExtendedVcdValueChangeSim : public VcdDumpRunTestBase {
 protected:
  std::string RunPortVcd(const std::string& src) {
    return RunVcdDump(src,
                      {.scope = "t",
                       .registration = VcdSignalRegistration::kContextFiltered,
                       .extended = true});
  }
};

TEST_F(ExtendedVcdValueChangeSim, ScalarPortValueChangeFormFromDumpports) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic hi;\n"
      "  logic lo;\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    hi = 1'b1;\n"
      "    lo = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$var port 1 <0 hi $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("$var port 1 <1 lo $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("p166 <0"), std::string::npos) << content;
  EXPECT_NE(content.find("p066 <1"), std::string::npos) << content;
  EXPECT_EQ(content.find("1!"), std::string::npos) << content;
  EXPECT_EQ(content.find("0!"), std::string::npos) << content;
}

TEST_F(ExtendedVcdValueChangeSim, WholeVectorPortValueChangeFromDumpports) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic [3:0] bus;\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    bus = 4'b1010;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$var port [3:0] <0 bus $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("p101066 <0"), std::string::npos) << content;
  EXPECT_EQ(content.find("b1010"), std::string::npos) << content;
}

TEST_F(ExtendedVcdValueChangeSim,
       StrengthComponentsFromDrivenAndFloatingPorts) {
  auto content = RunPortVcd(
      "module t;\n"
      "  wire floating;\n"
      "  logic driven;\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    driven = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("p166 <0"), std::string::npos) << content;
  EXPECT_NE(content.find("pF00 <1"), std::string::npos) << content;
}

TEST_F(ExtendedVcdValueChangeSim, DeclaredModulePortsUseValueChangeForm) {
  auto content = RunPortVcd(
      "module t(output o, output [3:0] bus);\n"
      "  assign o = 1'b1;\n"
      "  assign bus = 4'b0110;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_NE(content.find("$var port [3:0] <0 bus $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("$var port 1 <1 o $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("pLHHL66 <0"), std::string::npos) << content;
  EXPECT_NE(content.find("pH06 <1"), std::string::npos) << content;
}

TEST_F(ExtendedVcdValueChangeSim, PortIdentifierCodeIsMultiDigitInteger) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0;\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    b0 = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$var port 1 <10 b0 $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("p166 <10"), std::string::npos) << content;
}

TEST_F(ExtendedVcdValueChangeSim, PortWithNoVariableHasNoValueChange) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.SetExtendedPortNodes();
    vcd.WriteHeader("1ns");
    vcd.BeginScope("t");
    vcd.RegisterSignal("bare", 1, nullptr);
    auto* held = arena_.Create<Variable>();
    held->value = MakeLogic4VecVal(arena_, 1, 1);
    vcd.RegisterSignal("held", 1, held);
    vcd.EndScope();
    vcd.EndDefinitions();
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$var port 1 <0 bare $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("$dumpports\np166 <1\n$end"), std::string::npos)
      << content;
  EXPECT_EQ(content.find(" <0\n"), std::string::npos) << content;
}

class ExtendedVcdStrengthFromSource : public VcdDumpFromSourceTestBase {
 protected:
  std::string RunPortDump(const std::string& body) {
    RunSource("module t;\n" + body +
              "  initial begin\n"
              "    $dumpports(, \"strengths.vcd\");\n"
              "    #1;\n"
              "  end\n"
              "endmodule\n");
    return DumpFile("strengths.vcd");
  }

  static std::string PortIdentifierCode(const std::string& content,
                                        const std::string& name) {
    for (const auto& line : Lines(content)) {
      auto fields = Tokens(line);
      if (fields.size() != 6 || fields[0] != "$var" || fields[1] != "port") {
        continue;
      }
      if (fields[4] == name) return fields[3];
    }
    return "";
  }

  static std::string PortRecord(const std::string& content,
                                const std::string& name) {
    std::string code = PortIdentifierCode(content, name);
    if (code.empty()) return "<no-$var-port-" + name + ">";
    std::string record = "<no-change-" + code + ">";
    for (const auto& line : Lines(content)) {
      auto fields = Tokens(line);
      if (fields.size() != 2 || fields[0][0] != 'p' || fields[1] != code) {
        continue;
      }
      std::string body = fields[0].substr(1);
      if (body.size() < 3) return "<malformed-" + fields[0] + ">";
      record =
          body.substr(0, body.size() - 2) + "|" + body.substr(body.size() - 2);
    }
    return record;
  }
};

TEST_F(ExtendedVcdStrengthFromSource, PullDrivenNetReportsThePullDigit) {
  auto content = RunPortDump(
      "  wire w;\n"
      "  assign (pull0, pull1) w = 1'b1;\n");
  EXPECT_EQ(PortRecord(content, "w"), "1|05") << content;
}

TEST_F(ExtendedVcdStrengthFromSource,
       TwoNetsAtDifferentStrengthsGetDifferentRecords) {
  auto content = RunPortDump(
      "  wire pu;\n"
      "  wire we;\n"
      "  assign (pull0, pull1) pu = 1'b1;\n"
      "  assign (weak0, weak1) we = 1'b1;\n");
  EXPECT_EQ(PortRecord(content, "pu"), "1|05") << content;
  EXPECT_EQ(PortRecord(content, "we"), "1|03") << content;
  EXPECT_NE(PortRecord(content, "pu"), PortRecord(content, "we")) << content;
}

TEST_F(ExtendedVcdStrengthFromSource, SupplyNetReportsTheSupplyDigit) {
  auto content = RunPortDump("  supply1 vdd;\n");
  EXPECT_EQ(PortRecord(content, "vdd"), "1|07") << content;
}

TEST_F(ExtendedVcdStrengthFromSource,
       ResolvedStrengthOfTwoDriversReachesTheRecord) {
  auto content = RunPortDump(
      "  wire w;\n"
      "  assign (pull0, pull1) w = 1'b0;\n"
      "  assign (weak0, weak1) w = 1'b1;\n");
  EXPECT_EQ(PortRecord(content, "w"), "0|50") << content;
}

TEST_F(ExtendedVcdStrengthFromSource, VectorBitsAtTwoLevelsBothReachTheRecord) {
  auto content = RunPortDump(
      "  wire [1:0] w;\n"
      "  assign w = 2'b01;\n");
  EXPECT_EQ(PortRecord(content, "w"), "01|66") << content;
}

TEST_F(ExtendedVcdStrengthFromSource,
       AmbiguousResolvedStrengthReportsTheStrongerBound) {
  auto content = RunPortDump(
      "  wire w;\n"
      "  assign (weak0, weak1) w = 1'b1;\n"
      "  assign (weak0, weak1) w = 1'b0;\n");
  EXPECT_EQ(PortRecord(content, "w"), "?|33") << content;
}

}  // namespace
}  // namespace delta
