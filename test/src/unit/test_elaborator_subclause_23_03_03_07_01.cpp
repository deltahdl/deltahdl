
#include <gtest/gtest.h>

#include <string_view>

#include "common/types.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// Returns the resolved net type of the named net in the named elaborated
// module, or kNone when either is absent. Lets the interconnect-merge tests
// observe the built-in net type the interconnect net ends up with after the
// port connections are resolved (§23.3.3.7.1).
static NetType InterconnectNetType(RtlirDesign* design, std::string_view module,
                                   std::string_view net_name) {
  auto it = design->all_modules.find(module);
  if (it == design->all_modules.end()) return NetType::kNone;
  for (const auto& net : it->second->nets) {
    if (net.name == net_name) return net.net_type;
  }
  return NetType::kNone;
}

// §23.3.3.7.1: when only one side of a port connection is an interconnect net,
// the merged net takes the type of the other net. The interconnect net has no
// type of its own to contribute, so the merged simulated net adopts the child
// port's built-in net type. One test per admitted built-in net type -- each is
// a distinct input form that must be observed resolving to its own net type,
// not merely accepted without error. The external (instantiation-side)
// interconnect net is the one retyped, so its resolved type is inspected.

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

// §23.3.3.7.1 through the positional connection form: the merge and its type
// resolution apply the same way whether the port is named or ordered.
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

// §23.3.3.7.1 with an input-direction port: a port connection with an
// interconnect net still merges and resolves to the port's net type.
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

// §23.3.3.7.1 with an output-direction port: same merge and type resolution.
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

// §23.3.3.7.1: the interconnect net may be on the internal (child-port) side,
// with a built-in net type externally. The merge is legal; the external net is
// already its concrete type, so the connection elaborates without error.
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

// §23.3.3.7.1 (negative form): when both sides of the connection are
// interconnect, the merged net stays an interconnect net. An interconnect net
// type is illegal for a simulated net at the end of elaboration, so this is
// rejected.
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

// §23.3.3.7.1 (negative form) reached through a positional connection: two
// interconnect nets still merge to an interconnect net, which is illegal at the
// end of elaboration.
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

// §23.3.3.7.1 consuming §23.3.3.7 (Table 23-1 dominance): one interconnect net
// reaches a wire net in one child and a wand net in another, all built from
// real module/instance syntax. The single merged net resolves to the dominating
// type of the dissimilar built-in nets, which is wand.
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

// §23.3.3.7.1: the merging is transitive. An interconnect net joined to an
// interconnect port whose instance passes it on to a wire port is one net with
// that wire, so it is not of interconnect type at the end of elaboration,
// though the port joining the two interconnect nets has interconnect on both
// sides
// (#7388).
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

// §23.3.3.7.1: the wire the chain reaches may stand above it, a bit of it
// connected to the interconnect port that passes the net down to another
// interconnect port.
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

// §23.3.3.7.1: the wire may also be reached through a later sibling instance,
// whose port connection the merged net takes its type from after the first
// instance's interconnect port has joined it.
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

// §23.3.3.7.1 with §23.3.3.7.2: a gate terminal gives the interconnect net on
// it a net type of its own, and a chain reaching that net reaches the type.
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

// §23.3.3.7.1 (negative form): a chain of interconnect nets that reaches no net
// of another type anywhere is still of interconnect type at the end of
// elaboration, and is reported at each port joining two of its nets, however
// many other nets stand beside it.
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

// §23.3.3.7.1 with §23.2.2.3: an input port declared with a data type and no
// net type keyword is a net of the default net type, so the interconnect net
// connected to it merges into a wire (#7390).
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

// §23.3.3.7.1 with §23.2.2.3 and §22.8: the default net type in force where the
// port's module is defined is the one the merged net takes.
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

// §23.3.3.7.1: an output port declared with a data type alone is a variable
// (§23.2.2.3), no net, so it gives the interconnect net no net type.
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
}

// §23.3.3.7.1: the merging is transitive, so an interconnect net that reaches
// a typed net only through another module's interconnect port takes that
// net's type, and the typed net keeps its own. top.c meets mid's interconnect
// port p, which meets sink's tri port q (#7396).
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
  EXPECT_EQ(InterconnectNetType(design, "sink", "q"), NetType::kTri);
}

// §23.3.3.7.1 with Table 23-1: an interconnect chain reaching dissimilar typed
// nets through an interconnect port is one net of the dominating type among
// them, a wand over a wire whichever is connected first.
TEST(InterconnectPortConnectionElaboration,
     AnInterconnectChainTakesTheDominatingTypeItReaches) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module w_sink(inout wire q);\n"
      "endmodule\n"
      "module a_sink(inout wand q);\n"
      "endmodule\n"
      "module mid(interconnect p);\n"
      "  w_sink s1(p);\n"
      "  a_sink s2(p);\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect c;\n"
      "  mid m(c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(InterconnectNetType(design, "top", "c"), NetType::kWand);
}

}  // namespace
