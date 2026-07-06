#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(InterconnectElaboration, ForceIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect sig;\n"
      "  initial force sig = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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

// §6.6.8: an interconnect net shall not be used in any procedural context.
// Reading it on the RHS of a procedural (blocking) assignment is illegal even
// though the same read would be legal for an ordinary net.
TEST(InterconnectElaboration, ProceduralRhsReadIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  logic y;\n"
      "  initial y = ic;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §6.6.8: reading an interconnect net inside a procedural if-condition is an
// illegal use in a procedural context.
TEST(InterconnectElaboration, ProceduralConditionReadIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  logic y;\n"
      "  initial if (ic) y = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §6.6.8: an interconnect net used only as a select index inside a procedural
// read expression is still an illegal procedural use.
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
  EXPECT_TRUE(f.diag.HasErrors());
}

// §6.6.8 speaks of "a net or port declared as interconnect": an interconnect
// PORT is likewise a typeless/generic net. A module that declares an
// interconnect port elaborates and the port is recorded as interconnect
// (Claim A, port input form).
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

// §6.6.8: the procedural/expression-use prohibition applies to an interconnect
// PORT as well as a local net. Reading an interconnect port on the RHS of a
// procedural assignment is illegal (Claim B/C, port input form). Reading an
// ordinary net port there would be legal, so this isolates the interconnect
// rule rather than a generic port-direction rule.
TEST(InterconnectElaboration, ProceduralReadOfInterconnectPortIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(interconnect p);\n"
      "  logic y;\n"
      "  initial y = p;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §6.6.8: an interconnect PORT shall not be the target of a continuous
// assignment (Claim B, port input form).
TEST(InterconnectElaboration, ContAssignToInterconnectPortIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(interconnect p);\n"
      "  assign p = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
}

// An interconnect net stays valid even when its connections resolve to
// dissimilar net types. The dissimilar-net-type diagnostic that fires for
// ordinary nets is suppressed once an interconnect net is involved, so a
// connection that mixes wire and wand resolutions is accepted.
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

}  // namespace
