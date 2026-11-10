#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>

#include "common/types.h"
#include "fixture_elaborator.h"
#include "helpers_generate_block_items.h"
#include "helpers_reported_error.h"
#include "model_net_declaration.h"

using namespace delta;

namespace {

TEST(InterconnectElaboration, ContAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect sig;\n"
      "  assign sig = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interconnect net cannot be used in continuous "
                            "assignment",
                            3, "6.6.8"));
}

TEST(InterconnectElaboration, NoDataType) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.has_data_type = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(InterconnectElaboration, WithDimensionsOk) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(InterconnectElaboration, NoDriveStrength) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.has_drive_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(InterconnectElaboration, NoChargeStrength) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.has_charge_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(InterconnectElaboration, NoAssignment) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.has_assignment = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(InterconnectElaboration, OneDelayOk) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.delay_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(InterconnectElaboration, MultipleDelaysError) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.delay_count = 3;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(InterconnectElaboration, DeclNetTypeIsInterconnect) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect sig;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->nets.empty());
  EXPECT_EQ(mod->nets[0].net_type, NetType::kInterconnect);
}

TEST(InterconnectElaboration, ProceduralAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect sig;\n"
      "  initial sig = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "net 'sig' cannot be the target of a procedural assignment", 3, "10.4"));
}

TEST(InterconnectElaboration, ForceIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect sig;\n"
      "  initial force sig = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interconnect net cannot be used in procedural "
                            "continuous assignment",
                            3, "6.6.8"));
}

TEST(InterconnectElaboration, ForceOnInterconnectFromAlwaysLatchIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  logic x;\n"
      "  always_latch force ic = x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interconnect net cannot be used in procedural "
                            "continuous assignment",
                            4, "6.6.8"));
}

TEST(InterconnectElaboration, ReleaseIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect sig;\n"
      "  initial begin\n"
      "    release sig;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interconnect net cannot be used in procedural "
                            "continuous assignment",
                            4, "6.6.8"));
}

TEST(InterconnectElaboration, ProceduralContinuousAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect sig;\n"
      "  initial begin\n"
      "    assign sig = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interconnect net cannot be used in procedural "
                            "continuous assignment",
                            4, "6.6.8"));
}

TEST(InterconnectElaboration, DeassignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect sig;\n"
      "  initial begin\n"
      "    deassign sig;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interconnect net cannot be used in procedural "
                            "continuous assignment",
                            4, "6.6.8"));
}

TEST(InterconnectElaboration, NetAliasWithInterconnectOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect a, b;\n"
      "  alias a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(InterconnectElaboration, ProceduralRhsReadIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  logic y;\n"
      "  initial y = ic;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "interconnect net cannot be used in a procedural expression", 4,
      "6.6.8"));
}

TEST(InterconnectElaboration, ProceduralConditionReadIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  logic y;\n"
      "  initial if (ic) y = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "interconnect net cannot be used in a procedural expression", 4,
      "6.6.8"));
}

TEST(InterconnectElaboration, ProceduralReadViaSelectIndexIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  logic [3:0] mem;\n"
      "  logic y;\n"
      "  initial y = mem[ic];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "interconnect net cannot be used in a procedural expression", 5,
      "6.6.8"));
}

TEST(InterconnectElaboration, InterconnectPortDeclIsGeneric) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(interconnect p);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->ports.empty());
  EXPECT_TRUE(mod->ports[0].is_interconnect);
}

TEST(InterconnectElaboration, ProceduralReadOfInterconnectPortIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(interconnect p);\n"
      "  logic y;\n"
      "  initial y = p;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "interconnect net cannot be used in a procedural expression", 3,
      "6.6.8"));
}

TEST(InterconnectElaboration, ContAssignToInterconnectPortIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(interconnect p);\n"
      "  assign p = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interconnect net cannot be used in continuous "
                            "assignment",
                            2, "6.6.8"));
}

TEST(InterconnectElaboration, PackedDimDeclOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect [7:0] bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->nets.empty());
  EXPECT_EQ(mod->nets[0].net_type, NetType::kInterconnect);
}

TEST(InterconnectElaboration, ContAssignRhsUsingInterconnectIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  wire w;\n"
      "  assign w = ic;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interconnect net cannot be used in expression", 4,
                            "6.6.8"));
}

TEST(InterconnectElaboration, ResolvesToDissimilarNetTypesWildcard) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module drv_wire(output wire o);\n"
      "  assign o = 1'b1;\n"
      "endmodule\n"
      "module drv_wand(output wand o);\n"
      "  assign o = 1'b0;\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect o;\n"
      "  drv_wire u0(.*);\n"
      "  drv_wand u1(.*);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(InterconnectElaboration, ResolvesToDissimilarNetTypesImplicitNamed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module drv_wire(output wire o);\n"
      "  assign o = 1'b1;\n"
      "endmodule\n"
      "module drv_wand(output wand o);\n"
      "  assign o = 1'b0;\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect o;\n"
      "  drv_wire u0(.o);\n"
      "  drv_wand u1(.o);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(InterconnectElaboration,
     ProceduralContinuousAssignToAnInterconnectInAForkIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect sig;\n"
      "  initial fork\n"
      "    force sig = 1;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interconnect net cannot be used in procedural "
                            "continuous assignment",
                            4, "6.6.8"));
}

TEST(InterconnectElaboration, ReadOfAnInterconnectInARandcaseArmIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  logic y;\n"
      "  initial randcase\n"
      "    1 : y = ic;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "interconnect net cannot be used in a procedural expression", 5,
      "6.6.8"));
}

TEST(InterconnectElaboration, ForceOnAPlainNetInAForkIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  wire w;\n"
      "  initial fork\n"
      "    force w = 1'b1;\n"
      "  join\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

constexpr const char* kInContAssign =
    "interconnect net cannot be used in continuous assignment";
constexpr const char* kInProcContAssign =
    "interconnect net cannot be used in procedural continuous assignment";
constexpr const char* kInExpression =
    "interconnect net cannot be used in expression";

::testing::AssertionResult InterconnectUseReported(const std::string& src,
                                                   const char* message,
                                                   uint32_t line) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return ReportedError(f.diag.Diagnostics(), message, line, "6.6.8");
}

TEST(InterconnectElaboration, ContAssignTargetSelectOrElementIsError) {
  EXPECT_TRUE(
      InterconnectUseReported("module t(input logic a);\n"
                              "  interconnect [1:0] ic;\n"
                              "  wire w;\n"
                              "  assign ic[0] = a;\n"
                              "endmodule\n",
                              kInContAssign, 4));
  EXPECT_TRUE(
      InterconnectUseReported("module t(input logic [2:0] b);\n"
                              "  interconnect [1:0] ic;\n"
                              "  wire w;\n"
                              "  assign {ic, w} = b;\n"
                              "endmodule\n",
                              kInContAssign, 4));
  EXPECT_TRUE(
      InterconnectUseReported("module t(input logic a);\n"
                              "  interconnect [1:0] ic;\n"
                              "  wire [3:0] w;\n"
                              "  assign w[ic] = a;\n"
                              "endmodule\n",
                              kInContAssign, 4));
  EXPECT_TRUE(
      ElabOk("module t(input logic a);\n"
             "  interconnect [1:0] ic;\n"
             "  wire [3:0] w;\n"
             "  assign w[1] = a;\n"
             "endmodule\n"));
}

TEST(InterconnectElaboration, ProcContAssignTargetSelectOrElementIsError) {
  EXPECT_TRUE(
      InterconnectUseReported("module t;\n"
                              "  interconnect [1:0] ic;\n"
                              "  wire w;\n"
                              "  initial force ic[0] = 1'b1;\n"
                              "endmodule\n",
                              kInProcContAssign, 4));
  EXPECT_TRUE(
      InterconnectUseReported("module t;\n"
                              "  interconnect [1:0] ic;\n"
                              "  wire w;\n"
                              "  initial release {ic, w};\n"
                              "endmodule\n",
                              kInProcContAssign, 4));
}

constexpr const char* kChild =
    "module c(input wire a);\n"
    "endmodule\n"
    "module c2(input wire [1:0] a);\n"
    "endmodule\n";

TEST(InterconnectElaboration, PortConnectionExpressionIsError) {
  const std::string kHead = std::string(kChild) +
                            "module t;\n"
                            "  interconnect ic, ic2;\n"
                            "  wire w;\n";
  for (const char* inst :
       {"  c x(.a(~ic));\n", "  c x(.a(ic & w));\n", "  c x(~ic);\n",
        "  c x(.a((ic)));\n", "  c2 x(.a({ic, w}));\n", "  c2 x({w, ic});\n"}) {
    EXPECT_TRUE(
        InterconnectUseReported(kHead + inst + "endmodule\n", kInExpression, 8))
        << inst;
  }
  for (const char* inst : {"  c x(.a(ic));\n", "  c x(ic);\n",
                           "  c2 x(.a({ic, ic2}));\n", "  c x(.a(~w));\n"}) {
    EXPECT_TRUE(ElabOk(kHead + inst + "endmodule\n")) << inst;
  }
}

TEST(InterconnectElaboration, SelectOfAnInterconnectConnects) {
  const std::string kHead = std::string(kChild) +
                            "module t(input logic x);\n"
                            "  interconnect [1:0] icv;\n"
                            "  interconnect ica [2];\n"
                            "  wire [3:0] w;\n";
  for (const char* inst : {"  c u(.a(icv[1]));\n", "  c u(.a(ica[0]));\n",
                           "  c2 u(.a(icv[1:0]));\n", "  buf (icv[0], x);\n",
                           "  buf (ica[1], x);\n"}) {
    EXPECT_TRUE(ElabOk(kHead + inst + "endmodule\n")) << inst;
  }
  EXPECT_TRUE(InterconnectUseReported(kHead + "  c u(.a(w[icv]));\nendmodule\n",
                                      kInExpression, 9));
}

TEST(InterconnectElaboration, GateTerminalExpressionIsError) {
  const std::string kHead =
      "module t(input logic b);\n"
      "  interconnect ic;\n"
      "  wire o;\n";
  EXPECT_TRUE(InterconnectUseReported(kHead + "  and (o, ~ic, b);\nendmodule\n",
                                      kInExpression, 4));
  EXPECT_TRUE(InterconnectUseReported(
      kHead + "  and (o, ic | b, b);\nendmodule\n", kInExpression, 4));
  EXPECT_TRUE(ElabOk(kHead + "  and (o, ic, b);\nendmodule\n"));
}

TEST(InterconnectElaboration, ParameterDelayAndRangeAreExpressions) {
  EXPECT_TRUE(
      InterconnectUseReported("module c #(parameter P = 1) (input wire a);\n"
                              "endmodule\n"
                              "module t;\n"
                              "  interconnect ic;\n"
                              "  c #(.P(ic)) x(.a(ic));\n"
                              "endmodule\n",
                              kInExpression, 5));
  EXPECT_TRUE(
      InterconnectUseReported("module t(input logic b);\n"
                              "  interconnect ic;\n"
                              "  wire o;\n"
                              "  buf #(ic) (o, b);\n"
                              "endmodule\n",
                              kInExpression, 4));
  EXPECT_TRUE(
      InterconnectUseReported("module t(input logic b);\n"
                              "  interconnect ic;\n"
                              "  wire o;\n"
                              "  buf g[ic:0] (o, b);\n"
                              "endmodule\n",
                              kInExpression, 4));
  EXPECT_TRUE(
      ElabOk("module c #(parameter P = 1) (input wire a);\n"
             "endmodule\n"
             "module t;\n"
             "  interconnect ic;\n"
             "  c #(.P(2)) x(.a(ic));\n"
             "endmodule\n"));
}

TEST(InterconnectElaboration, PortInterfaceAndGenerateBlockForms) {
  EXPECT_TRUE(
      InterconnectUseReported("module m(interconnect [1:0] p, input logic a);\n"
                              "  assign p[0] = a;\n"
                              "endmodule\n",
                              kInContAssign, 2));
  EXPECT_TRUE(InterconnectUseReported(std::string(kChild) +
                                          "module m(interconnect p);\n"
                                          "  c x(.a(~p));\n"
                                          "endmodule\n",
                                      kInExpression, 6));
  EXPECT_TRUE(
      InterconnectUseReported("interface i(input logic a);\n"
                              "  interconnect [1:0] ic;\n"
                              "  assign ic[0] = a;\n"
                              "endinterface\n"
                              "module t(input logic a);\n"
                              "  i x(a);\n"
                              "endmodule\n",
                              kInContAssign, 3));
  EXPECT_TRUE(
      InterconnectUseReported("module t(input logic a);\n"
                              "  interconnect [1:0] ic;\n"
                              "  if (1) begin : g\n"
                              "    assign ic[0] = a;\n"
                              "  end\n"
                              "endmodule\n",
                              kInContAssign, 4));
  EXPECT_TRUE(
      InterconnectUseReported("module t(input logic a);\n"
                              "  if (1) begin : g\n"
                              "    interconnect ic;\n"
                              "    assign ic = a;\n"
                              "  end\n"
                              "endmodule\n",
                              kInContAssign, 4));
  EXPECT_TRUE(InterconnectUseReported(std::string(kChild) +
                                          "module t;\n"
                                          "  interconnect ic;\n"
                                          "  if (1) begin : g\n"
                                          "    c x(.a(~ic));\n"
                                          "  end\n"
                                          "endmodule\n",
                                      kInExpression, 8));
  EXPECT_TRUE(ElabOk(std::string(kChild) + "module t;\n"
                                           "  interconnect ic;\n"
                                           "  if (1) begin : g\n"
                                           "    c x(.a(ic));\n"
                                           "  end\n"
                                           "endmodule\n"));
}

TEST(InterconnectElaboration, ProceduralUseInsideGenerateBlocksIsRejected) {
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "interconnect ic; logic y;", "initial y = ic;"},
      "interconnect net cannot be used in a procedural expression", "6.6.8"));
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "interconnect ic;", "initial force ic = 1;"},
      "interconnect net cannot be used in procedural continuous assignment",
      "6.6.8"));
  EXPECT_TRUE(AcceptedInsideGenerateBlocks(
      {"", "interconnect ic; logic y, z;", "initial y = z;"}));
}

struct ItemPlace {
  const char* head;
  const char* tail;
};

constexpr ItemPlace kModulePlace{"module t;\n", "endmodule\n"};
constexpr ItemPlace kInterfacePlace{
    "interface t;\n", "endinterface\nmodule top;\n  t x();\nendmodule\n"};
constexpr ItemPlace kProgramPlace{
    "program t;\n", "endprogram\nmodule top;\n  t x();\nendmodule\n"};
constexpr ItemPlace kGeneratePlace{"module t;\n  if (1) begin : g\n",
                                   "  end\nendmodule\n"};
constexpr std::initializer_list<ItemPlace> kEveryPlace = {
    kModulePlace, kInterfacePlace, kProgramPlace, kGeneratePlace};
constexpr std::initializer_list<ItemPlace> kEveryPlaceButAProgram = {
    kModulePlace, kInterfacePlace, kGeneratePlace};

constexpr const char* kInProceduralExpression =
    "interconnect net cannot be used in a procedural expression";

::testing::AssertionResult LastLineReportedInEachPlace(
    std::initializer_list<ItemPlace> places, const std::string& prefix,
    const std::string& body, std::string_view message,
    std::string_view subclause = "6.6.8") {
  for (const ItemPlace& place : places) {
    std::string src = prefix;
    src += place.head;
    src += body;
    const auto kLine = static_cast<uint32_t>(std::ranges::count(src, '\n'));
    src += place.tail;
    ElabFixture f;
    ElaborateSrc(src, f);
    auto reported =
        ReportedError(f.diag.Diagnostics(), message, kLine, subclause);
    if (!reported) return reported << "\nin\n" << src;
  }
  return ::testing::AssertionSuccess();
}

::testing::AssertionResult AcceptedInEachPlace(
    std::initializer_list<ItemPlace> places, const std::string& prefix,
    const std::string& body) {
  for (const ItemPlace& place : places) {
    std::string src = prefix;
    src += place.head;
    src += body;
    src += place.tail;
    if (!ElabOk(src)) {
      return ::testing::AssertionFailure() << "rejected\n" << src;
    }
  }
  return ::testing::AssertionSuccess();
}

TEST(InterconnectElaboration,
     DISABLED_NetDeclarationAssignmentReadingAnInterconnectIsError) {
  EXPECT_TRUE(LastLineReportedInEachPlace(
      kEveryPlace, "", "  interconnect ic;\n  wire w = ic;\n", kInExpression));
  EXPECT_TRUE(
      AcceptedInEachPlace(kEveryPlace, "", "  wire x;\n  wire w = x;\n"));
}

TEST(InterconnectElaboration,
     DISABLED_VariableInitializerReadingAnInterconnectIsError) {
  EXPECT_TRUE(LastLineReportedInEachPlace(
      kEveryPlace, "", "  interconnect ic;\n  logic v = ic;\n", kInExpression));
  EXPECT_TRUE(
      AcceptedInEachPlace(kEveryPlace, "", "  wire x;\n  logic v = x;\n"));
}

TEST(InterconnectElaboration,
     DISABLED_SubroutineBodyReadingForcingOrReleasingAnInterconnectIsError) {
  EXPECT_TRUE(LastLineReportedInEachPlace(
      kEveryPlace, "",
      "  interconnect ic;\n"
      "  function logic f(); return ic; endfunction\n",
      kInProceduralExpression));
  EXPECT_TRUE(
      LastLineReportedInEachPlace(kEveryPlace, "",
                                  "  interconnect ic;\n"
                                  "  task k(); force ic = 1'b1; endtask\n",
                                  kInProcContAssign));
  EXPECT_TRUE(LastLineReportedInEachPlace(kEveryPlace, "",
                                          "  interconnect ic;\n"
                                          "  task k(); release ic; endtask\n",
                                          kInProcContAssign));
  EXPECT_TRUE(
      AcceptedInEachPlace(kEveryPlace, "",
                          "  wire x;\n"
                          "  function logic f(); return x; endfunction\n"
                          "  task k(); force x = 1'b1; endtask\n"
                          "  task r(); release x; endtask\n"));
}

TEST(InterconnectElaboration, SubroutineBodyAssigningAnInterconnectIsError) {
  EXPECT_TRUE(LastLineReportedInEachPlace(
      kEveryPlace, "",
      "  interconnect ic;\n"
      "  function void f(); ic = 1'b1; endfunction\n",
      "net 'ic' cannot be the target of a procedural assignment", "10.4"));
  EXPECT_TRUE(
      AcceptedInEachPlace(kEveryPlace, "",
                          "  logic v;\n"
                          "  function void f(); v = 1'b1; endfunction\n"));
}

TEST(InterconnectElaboration,
     DISABLED_EventControlNamingAnInterconnectIsError) {
  for (const char* item : {"  initial @(ic);\n", "  initial @(posedge ic);\n",
                           "  initial @(negedge ic);\n"}) {
    EXPECT_TRUE(LastLineReportedInEachPlace(
        kEveryPlace, "", std::string("  interconnect ic;\n") + item,
        kInProceduralExpression));
  }
  for (const char* item : {"  always @(ic) y = 1'b1;\n",
                           "  always_ff @(posedge ic) y <= 1'b1;\n"}) {
    EXPECT_TRUE(LastLineReportedInEachPlace(
        kEveryPlaceButAProgram, "",
        std::string("  interconnect ic;\n  logic y;\n") + item,
        kInProceduralExpression));
  }
  EXPECT_TRUE(AcceptedInEachPlace(kEveryPlace, "",
                                  "  wire x;\n"
                                  "  initial @(x);\n"
                                  "  initial @(posedge x);\n"
                                  "  initial @(negedge x);\n"));
  EXPECT_TRUE(AcceptedInEachPlace(kEveryPlaceButAProgram, "",
                                  "  wire x;\n"
                                  "  logic y, z;\n"
                                  "  always @(x) y = 1'b1;\n"
                                  "  always_ff @(posedge x) z <= 1'b1;\n"));
}

TEST(InterconnectElaboration, WaitConditionReadingAnInterconnectIsError) {
  EXPECT_TRUE(LastLineReportedInEachPlace(
      kEveryPlace, "", "  interconnect ic;\n  initial wait (ic);\n",
      kInProceduralExpression));
  EXPECT_TRUE(
      AcceptedInEachPlace(kEveryPlace, "", "  wire x;\n  initial wait (x);\n"));
}

TEST(InterconnectElaboration,
     DISABLED_AssertionOrItsDeclarationReadingAnInterconnectIsError) {
  for (const char* item :
       {"  assert property (@(posedge clk) ic);\n",
        "  assume property (@(posedge clk) ic);\n",
        "  cover property (@(posedge clk) ic);\n",
        "  restrict property (@(posedge clk) ic);\n",
        "  sequence s; ic; endsequence\n", "  property p; ic; endproperty\n",
        "  let l = ic;\n"}) {
    EXPECT_TRUE(LastLineReportedInEachPlace(
        kEveryPlace, "",
        std::string("  interconnect ic;\n  logic clk;\n") + item,
        kInExpression));
  }
  EXPECT_TRUE(AcceptedInEachPlace(kEveryPlace, "",
                                  "  wire x;\n"
                                  "  logic clk;\n"
                                  "  assert property (@(posedge clk) x);\n"
                                  "  sequence s; x; endsequence\n"
                                  "  let l = x;\n"));
}

TEST(InterconnectElaboration, DISABLED_CovergroupNamingAnInterconnectIsError) {
  EXPECT_TRUE(LastLineReportedInEachPlace(
      kEveryPlace, "",
      "  interconnect ic;\n"
      "  logic clk;\n"
      "  covergroup cg @(posedge clk); coverpoint ic; endgroup\n",
      kInExpression));
  EXPECT_TRUE(LastLineReportedInEachPlace(
      kEveryPlace, "",
      "  interconnect ic;\n"
      "  logic a;\n"
      "  covergroup cg @(posedge ic); coverpoint a; endgroup\n",
      kInExpression));
  EXPECT_TRUE(AcceptedInEachPlace(kEveryPlace, "",
                                  "  wire x;\n"
                                  "  covergroup cg @(posedge x); coverpoint x; "
                                  "endgroup\n"));
}

TEST(InterconnectElaboration,
     DISABLED_ClockingBlockNamingAnInterconnectIsError) {
  EXPECT_TRUE(LastLineReportedInEachPlace(
      kEveryPlace, "",
      "  interconnect ic;\n"
      "  logic a;\n"
      "  clocking cb @(posedge ic); input a; endclocking\n",
      kInExpression));
  EXPECT_TRUE(LastLineReportedInEachPlace(
      kEveryPlace, "",
      "  interconnect ic;\n"
      "  logic clk;\n"
      "  clocking cb @(posedge clk); input ic; endclocking\n",
      kInExpression));
  EXPECT_TRUE(AcceptedInEachPlace(
      kEveryPlace, "",
      "  wire x, y;\n"
      "  clocking cb @(posedge x); input y; endclocking\n"));
}

TEST(InterconnectElaboration,
     DISABLED_CheckerArgumentThatIsAnInterconnectIsError) {
  const std::string kCheckers =
      "checker ci(input logic a);\n"
      "endchecker\n"
      "checker co(output logic a);\n"
      "endchecker\n";
  EXPECT_TRUE(LastLineReportedInEachPlace(kEveryPlaceButAProgram, kCheckers,
                                          "  interconnect ic;\n  ci x(ic);\n",
                                          kInExpression));
  EXPECT_TRUE(LastLineReportedInEachPlace(kEveryPlaceButAProgram, kCheckers,
                                          "  interconnect ic;\n  co x(ic);\n",
                                          kInExpression));
  EXPECT_TRUE(AcceptedInEachPlace(kEveryPlaceButAProgram, kCheckers,
                                  "  wire w;\n  ci x(w);\n  co y(w);\n"));
}

TEST(InterconnectElaboration,
     DISABLED_SpecifyBlockNamingAnInterconnectPortIsError) {
  EXPECT_TRUE(
      InterconnectUseReported("module t(input interconnect a, output wire b);\n"
                              "  specify (a => b) = 1; endspecify\n"
                              "endmodule\n",
                              kInExpression, 2));
  EXPECT_TRUE(
      InterconnectUseReported("module t(input interconnect a, input wire b);\n"
                              "  specify $setup(a, posedge b, 1); endspecify\n"
                              "endmodule\n",
                              kInExpression, 2));
  EXPECT_TRUE(
      ElabOk("module t(input wire a, output wire b, input wire c);\n"
             "  specify (a => b) = 1; $setup(a, posedge c, 1); endspecify\n"
             "endmodule\n"));
}

}  // namespace
