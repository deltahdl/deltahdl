#include <gtest/gtest.h>

#include <string>

#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DissimilarNetTypePortConnectionElaboration, WireToWireNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration, WandToWandNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wand a);\n"
      "endmodule\n"
      "module top;\n"
      "  wand w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration, WorToWorNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wor a);\n"
      "endmodule\n"
      "module top;\n"
      "  wor w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration, TriregToTriregNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout trireg a);\n"
      "endmodule\n"
      "module top;\n"
      "  trireg w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration, Tri0ToTri0NoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout tri0 a);\n"
      "endmodule\n"
      "module top;\n"
      "  tri0 w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration, Tri1ToTri1NoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout tri1 a);\n"
      "endmodule\n"
      "module top;\n"
      "  tri1 w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalWireExternalWandNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  wand w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalWireExternalSupply0NoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  supply0 w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalTriregExternalTri0NoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout trireg a);\n"
      "endmodule\n"
      "module top;\n"
      "  tri0 w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalTriregExternalTri1NoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout trireg a);\n"
      "endmodule\n"
      "module top;\n"
      "  tri1 w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalWandExternalSupply1NoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wand a);\n"
      "endmodule\n"
      "module top;\n"
      "  supply1 w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalUwireExternalUwireNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout uwire a);\n"
      "endmodule\n"
      "module top;\n"
      "  uwire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalWandExternalWireNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wand a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalWorExternalWireNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wor a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalTriregExternalWireNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout trireg a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalTri0ExternalTriregNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout tri0 a);\n"
      "endmodule\n"
      "module top;\n"
      "  trireg w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalSupply0ExternalWireNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout supply0 a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalSupply0ExternalTriregNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout supply0 a);\n"
      "endmodule\n"
      "module top;\n"
      "  trireg w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalSupply1ExternalWireNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout supply1 a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration, InternalWandExternalWorWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wand a);\n"
      "endmodule\n"
      "module top;\n"
      "  wor w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration, InternalWorExternalWandWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wor a);\n"
      "endmodule\n"
      "module top;\n"
      "  wand w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalTriregExternalWandWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout trireg a);\n"
      "endmodule\n"
      "module top;\n"
      "  wand w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalTriregExternalWorWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout trireg a);\n"
      "endmodule\n"
      "module top;\n"
      "  wor w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalTri0ExternalTri1Warns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout tri0 a);\n"
      "endmodule\n"
      "module top;\n"
      "  tri1 w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalTri1ExternalTri0Warns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout tri1 a);\n"
      "endmodule\n"
      "module top;\n"
      "  tri0 w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalTri0ExternalWandWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout tri0 a);\n"
      "endmodule\n"
      "module top;\n"
      "  wand w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalSupply0ExternalSupply1Warns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout supply0 a);\n"
      "endmodule\n"
      "module top;\n"
      "  supply1 w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalSupply1ExternalSupply0Warns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout supply1 a);\n"
      "endmodule\n"
      "module top;\n"
      "  supply0 w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalUwireExternalWandWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout uwire a);\n"
      "endmodule\n"
      "module top;\n"
      "  wand w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalUwireExternalWorWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout uwire a);\n"
      "endmodule\n"
      "module top;\n"
      "  wor w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalUwireExternalTriregWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout uwire a);\n"
      "endmodule\n"
      "module top;\n"
      "  trireg w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalUwireExternalTri0Warns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout uwire a);\n"
      "endmodule\n"
      "module top;\n"
      "  tri0 w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalUwireExternalTri1Warns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout uwire a);\n"
      "endmodule\n"
      "module top;\n"
      "  tri1 w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     TriandBehavesAsWandInternalDominatesWireNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout triand a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     TriorBehavesAsWorExternalWandWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout trior a);\n"
      "endmodule\n"
      "module top;\n"
      "  wand w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     TriBehavesAsWireExternalWandNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout tri a);\n"
      "endmodule\n"
      "module top;\n"
      "  wand w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     NeitherDominatesExternalTypeUsedWithWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wand a);\n"
      "endmodule\n"
      "module top;\n"
      "  trireg w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InputPortDissimilarNetTypesWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input wand a);\n"
      "endmodule\n"
      "module top;\n"
      "  wor w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     OutputPortDissimilarNetTypesWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(output trireg a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wor w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     PositionalConnectionDissimilarNetTypesWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wand a);\n"
      "endmodule\n"
      "module top;\n"
      "  wor w;\n"
      "  child u(w);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalWandExternalUwireWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wand a);\n"
      "endmodule\n"
      "module top;\n"
      "  uwire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalWireExternalUwireNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  uwire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalWandExternalTriNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wand a);\n"
      "endmodule\n"
      "module top;\n"
      "  tri w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalWorExternalTriandWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wor a);\n"
      "endmodule\n"
      "module top;\n"
      "  triand w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalWandExternalTriorWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wand a);\n"
      "endmodule\n"
      "module top;\n"
      "  trior w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

static NetType ElaboratedNetType(RtlirDesign* design, std::string_view module,
                                 std::string_view net_name) {
  auto it = design->all_modules.find(module);
  if (it == design->all_modules.end()) return NetType::kNone;
  for (const auto& net : it->second->nets) {
    if (net.name == net_name) return net.net_type;
  }
  return NetType::kNone;
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalWandDominatesCollapsedNetBecomesWand) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wand a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ElaboratedNetType(design, "top", "w"), NetType::kWand);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     InternalTriregDominatesCollapsedNetBecomesTrireg) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout trireg a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ElaboratedNetType(design, "top", "w"), NetType::kTrireg);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     ExternalWandDominatesCollapsedNetStaysWand) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  wand w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ElaboratedNetType(design, "top", "w"), NetType::kWand);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     NeitherDominatesCollapsedNetKeepsExternalTrireg) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wand a);\n"
      "endmodule\n"
      "module top;\n"
      "  trireg w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ElaboratedNetType(design, "top", "w"), NetType::kTrireg);
}

TEST(DissimilarNetTypePortConnectionElaboration,
     DataTypedInputOfTheDefaultNetTypeDominatesExternalWire) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_nettype wand\n"
      "module child(input logic a);\n"
      "endmodule\n"
      "`default_nettype wire\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ElaboratedNetType(design, "top", "w"), NetType::kWand);
}

struct NetKindEntry {
  const char* keyword;
  NetType type;
  int group;
};

constexpr NetKindEntry kTableNetKinds[] = {
    {"wire", NetType::kWire, 0},       {"tri", NetType::kTri, 0},
    {"wand", NetType::kWand, 1},       {"triand", NetType::kTriand, 1},
    {"wor", NetType::kWor, 2},         {"trior", NetType::kTrior, 2},
    {"trireg", NetType::kTrireg, 3},   {"tri0", NetType::kTri0, 4},
    {"tri1", NetType::kTri1, 5},       {"uwire", NetType::kUwire, 6},
    {"supply0", NetType::kSupply0, 7}, {"supply1", NetType::kSupply1, 8},
};

constexpr const char* kResultingNetTable[9] = {
    "EEEEEEEEE", "IEXXXXXEE", "IXEXXXXEE", "IXXEEEXEE", "IXXIEXXEE",
    "IXXIXEXEE", "IJJJJJEEE", "IIIIIIIEX", "IIIIIIIXE",
};

TEST(DissimilarNetTypePortConnectionElaboration,
     EveryPairTakesTheTablesNetTypeAndWarning) {
  for (const auto& internal : kTableNetKinds) {
    for (const auto& external : kTableNetKinds) {
      if (internal.group == external.group) continue;
      char entry = kResultingNetTable[internal.group][external.group];
      bool uses_internal = entry == 'I' || entry == 'J';
      bool warns = entry == 'X' || entry == 'J';
      ElabFixture f;
      auto* design =
          ElaborateSrc(std::string("module child(inout ") + internal.keyword +
                           " a);\n"
                           "endmodule\n"
                           "module top;\n  " +
                           external.keyword +
                           " w;\n"
                           "  child u(.a(w));\n"
                           "endmodule\n",
                       f);
      std::string pair = std::string(internal.keyword) + " inside, " +
                         external.keyword + " outside";
      ASSERT_NE(design, nullptr) << pair;
      EXPECT_FALSE(f.has_errors) << pair;
      EXPECT_EQ(ElaboratedNetType(design, "top", "w"),
                uses_internal ? internal.type : external.type)
          << pair;
      bool warned = false;
      for (const auto& d : f.diag.Diagnostics()) {
        warned = warned || (d.severity == DiagSeverity::kWarning &&
                            d.loc.line == 5 && d.subclause == "23.3.3.7");
      }
      EXPECT_EQ(warned, warns) << pair;
    }
  }
}

}  // namespace
