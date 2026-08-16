#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
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

// A blocking assignment whose target is an interconnect net is rejected by the
// §6.5 rule against a net as a procedural-assignment target, not by a report of
// its own: no §6.6.8 site names this shape, because the interconnect net is a
// net and §6.5 already forbids it.
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
      "net 'sig' cannot be the target of a procedural assignment", 3, "6.5"));
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

// The same force, moved out of `initial` and into `always_latch`. §9.2.2.3
// makes an always_latch procedure a structured procedure like any other, and
// §6.6.8 forbids the interconnect net in a procedural continuous assignment
// whichever keyword introduced the procedure.
// Elaborator::ValidateItemConstraints decides which module items carry a
// procedural body, so a case that only ever writes `initial` or `always` cannot
// tell whether the other four kinds reach CheckInterconnectProcContAssign at
// all.
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "interconnect net cannot be used in a procedural expression", 4,
      "6.6.8"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "interconnect net cannot be used in a procedural expression", 4,
      "6.6.8"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "interconnect net cannot be used in a procedural expression", 5,
      "6.6.8"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "interconnect net cannot be used in a procedural expression", 3,
      "6.6.8"));
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
  // The RHS-use report, not the LHS-target one: the target `w` is an ordinary
  // wire, so only the interconnect read on the right is illegal.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interconnect net cannot be used in expression", 4,
                            "6.6.8"));
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

// The .name counterpart of the case above. §23.3.3.7.1 exempts a connection to
// an interconnect net whatever the connection syntax, and this form runs a
// stricter check than the ordered one -- §23.3.2.3 makes the implicit .name
// form an error where an explicit connection would only warn -- so the
// exemption has to be honoured here too.
//
// Both tests need two instances to mean anything. §23.3.3.7.1 merges each
// connection into the net as it is bound, so the first one leaves a concrete
// type behind and only the second can be judged against it. One instance would
// pass without the exemption ever being consulted.
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

// §6.6.8's rule against an interconnect net in a procedural continuous
// assignment is decided by the statement, not by where the statement stands,
// and §9.3.2 makes a par_block a statement_or_null. ForceIsError above writes
// the same force directly under `initial` and expects the same report;
// CheckInterconnectProcContAssign skipped Stmt::fork_stmts before it recursed
// through ForEachChildStmt, so that case could not tell whether a fork member
// was reached at all.
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

// §6.6.8's rule against reading an interconnect net in a procedural expression
// is decided by the expression, not by where the statement stands, and §18.16
// makes each randcase_item's body a statement_or_null.
// ProceduralRhsReadIsError above writes the same assignment directly under
// `initial` and expects the same report; CheckInterconnectProceduralRead
// skipped Stmt::randcase_items before it recursed through ForEachChildStmt.
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

// The regression against a walk that reports on every statement it newly
// reaches: §9.3.2 makes a par_block a statement_or_null, so both walkers now
// descend into a fork member, and forcing an ordinary wire there is what
// §6.6.8 leaves alone. The module declares an interconnect net as well, so the
// set of interconnect names both walkers test against is non-empty and the
// acceptance is the rule's answer rather than an empty set's.
// ProceduralContinuousAssignToAnInterconnectInAForkIsRejected above writes the
// same fork with an interconnect target.
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

}  // namespace
