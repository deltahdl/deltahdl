#include <gtest/gtest.h>

#include <format>
#include <string>
#include <string_view>

#include "common/types.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

static NetType InterconnectNetType(RtlirDesign* design, std::string_view module,
                                   std::string_view net_name) {
  auto it = design->all_modules.find(module);
  if (it == design->all_modules.end()) return NetType::kNone;
  for (const auto& net : it->second->nets) {
    if (net.name == net_name) return net.net_type;
  }
  return NetType::kNone;
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectResolvesToWireType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "ic"), NetType::kWire);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectResolvesToTriType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout tri a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "ic"), NetType::kTri);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectResolvesToWandType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wand a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "ic"), NetType::kWand);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectResolvesToTriandType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout triand a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "ic"), NetType::kTriand);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectResolvesToWorType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wor a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "ic"), NetType::kWor);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectResolvesToTriorType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout trior a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "ic"), NetType::kTrior);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectResolvesToTri0Type) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout tri0 a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "ic"), NetType::kTri0);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectResolvesToTri1Type) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout tri1 a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "ic"), NetType::kTri1);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectResolvesToTriregType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout trireg a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "ic"), NetType::kTrireg);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectResolvesToUwireType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout uwire a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "ic"), NetType::kUwire);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectResolvesToSupply0Type) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout supply0 a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "ic"), NetType::kSupply0);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectResolvesToSupply1Type) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout supply1 a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "ic"), NetType::kSupply1);
}

TEST(InterconnectPortConnectionElaboration,
     PositionalExternalInterconnectResolvesToWireType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(ic);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "ic"), NetType::kWire);
}

TEST(InterconnectPortConnectionElaboration,
     InputPortExternalInterconnectResolvesToWireType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "ic"), NetType::kWire);
}

TEST(InterconnectPortConnectionElaboration,
     OutputPortExternalInterconnectResolvesToWireType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(output wire a);\n"
      "  assign a = 1'b0;\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "ic"), NetType::kWire);
}

TEST(InterconnectPortConnectionElaboration,
     InternalInterconnectExternalWireNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout interconnect a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     InternalInterconnectExternalWandNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout interconnect a);\n"
      "endmodule\n"
      "module top;\n"
      "  wand w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     BothInterconnectIllegalAtEndOfElaboration) {
  ElabFixture f;
  ElaborateSrc(
      "module child(inout interconnect a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "simulated net for port 'a' of instance 'u' has "
                            "interconnect type at end of elaboration",
                            5, "23.3.3.7.1"));
}

TEST(InterconnectPortConnectionElaboration,
     PositionalBothInterconnectIllegalAtEndOfElaboration) {
  ElabFixture f;
  ElaborateSrc(
      "module child(inout interconnect a);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(ic);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "simulated net for port 'a' of instance 'u' has "
                            "interconnect type at end of elaboration",
                            5, "23.3.3.7.1"));
}

TEST(InterconnectPortConnectionElaboration,
     InterconnectMergedAcrossDissimilarPortsResolvesToWand) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module dut1(inout wire w);\n"
      "  assign w = 1;\n"
      "endmodule\n"
      "module dut2(inout wand w);\n"
      "  assign w = 0;\n"
      "endmodule\n"
      "module netlist;\n"
      "  interconnect iwire;\n"
      "  dut1 child1(iwire);\n"
      "  dut2 child2(iwire);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "netlist", "iwire"), NetType::kWand);
}

TEST(InterconnectPortConnectionElaboration,
     InterconnectChainReachingAWireBelowIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module sink(input wire q);\n"
      "endmodule\n"
      "module mid(interconnect p);\n"
      "  sink s(p);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect c;\n"
      "  mid m(c);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     InterconnectChainReachingAWireAboveIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf(interconnect p);\n"
      "endmodule\n"
      "module mid(interconnect p);\n"
      "  leaf l(p);\n"
      "endmodule\n"
      "module top;\n"
      "  wire [1:0] w;\n"
      "  mid m(w[0]);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     InterconnectChainReachingAWireThroughASiblingIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf(interconnect p);\n"
      "endmodule\n"
      "module sink(input wire q);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect c;\n"
      "  leaf u(c);\n"
      "  sink v(c);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     InterconnectChainReachingAGateTerminalIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module mid(interconnect p);\n"
      "  wire a, b;\n"
      "  and g(p, a, b);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect c;\n"
      "  mid m(c);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterconnectPortConnectionElaboration,
     InterconnectChainReachingNoOtherTypeIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf(interconnect p);\n"
      "endmodule\n"
      "module mid(interconnect p);\n"
      "  leaf l(p);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  interconnect c;\n"
      "  mid m(c);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "simulated net for port 'p' of instance 'm' has "
                            "interconnect type at end of elaboration",
                            9, "23.3.3.7.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "simulated net for port 'p' of instance 'l' has "
                            "interconnect type at end of elaboration",
                            4, "23.3.3.7.1"));
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectOnADataTypedInputResolvesToWire) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sink(input logic q);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect c;\n"
      "  sink v(c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "c"), NetType::kWire);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectOnADataTypedInputTakesTheDefaultNetType) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_nettype tri\n"
      "module sink(input logic q);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect c;\n"
      "  sink v(c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(InterconnectNetType(design, "top", "c"), NetType::kTri);
}

TEST(InterconnectPortConnectionElaboration,
     ExternalInterconnectOnAVariablePortGetsNoNetType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module src(output logic q);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect c;\n"
      "  src u(c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(InterconnectNetType(design, "top", "c"), NetType::kInterconnect);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "port variable 'q' cannot be connected to interconnect 'c'",
                    5, "23.3.3.2"));
}

TEST(InterconnectPortConnectionElaboration,
     AnInterconnectChainTakesTheTypeOfTheNetItReaches) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sink(inout tri q);\n"
      "endmodule\n"
      "module mid(interconnect p);\n"
      "  sink s(p);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect c;\n"
      "  mid m(c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "c"), NetType::kTri);
  auto sink = design->all_modules.find("sink");
  ASSERT_NE(sink, design->all_modules.end());
  ASSERT_EQ(sink->second->ports.size(), 1u);
  EXPECT_EQ(sink->second->ports[0].net_type, NetType::kTri);
}

static NetType ChainTypeReachingSinks(std::string_view first,
                                      std::string_view second) {
  ElabFixture f;
  const std::string kSrc = std::format(
                               "module a_sink(inout {} q);\nendmodule\n"
                               "module b_sink(inout {} q);\nendmodule\n",
                               first, second) +
                           "module mid(interconnect p);\n"
                           "  a_sink s1(p);\n"
                           "  b_sink s2(p);\n"
                           "endmodule\n"
                           "module top;\n"
                           "  interconnect c;\n"
                           "  mid m(c);\n"
                           "endmodule\n";
  auto* design = ElaborateSrc(kSrc, f);
  if (design == nullptr || f.has_errors) return NetType::kNone;
  return InterconnectNetType(design, "top", "c");
}

TEST(InterconnectPortConnectionElaboration,
     AnInterconnectChainTakesTheDominatingTypeItReaches) {
  EXPECT_EQ(ChainTypeReachingSinks("wire", "wand"), NetType::kWand);
}

TEST(InterconnectPortConnectionElaboration,
     AnInterconnectChainKeepsTheDominatingTypeItReachesFirst) {
  EXPECT_EQ(ChainTypeReachingSinks("wand", "wire"), NetType::kWand);
}

}  // namespace
