#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_elaborator.h"
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

// A blocking assignment whose target is an interconnect net is rejected by
// §10.4's requirement that a procedural assignment's left-hand side be a
// variable, not by a report of its own: no §6.6.8 site names this shape,
// because the interconnect net is a net and a net is none of the four forms
// §10.4 admits.
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

// §6.6.8 speaks of a net or port declared as interconnect: an interconnect PORT
// is likewise a typeless/generic net. A module that declares an interconnect
// port elaborates and the port is recorded as interconnect (Claim A, port input
// form).
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

// §6.6.8 keeps an interconnect out of every continuous assignment, wherever
// the target writes it: selected, as an element of a concatenation, or in a
// select's index.
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

// A procedural continuous assignment is barred the same way, a selected
// interconnect or one in a concatenation among them.
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

// A port connection may be an interconnect only as a net_lvalue all of whose
// nets are interconnects: an operator over one, a concatenation with a wire
// and a parenthesized one are expressions, named or positional.
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

// A select of an interconnect vector or array is a net_lvalue of interconnects
// alone, as a port connection and as a terminal; a select whose index reads an
// interconnect is not.
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

// A gate's terminal is a connection too: an interconnect as a terminal is one,
// and an expression over it is not.
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

// A parameter value, a delay and an instance array's range are expressions
// that connect nothing, where an interconnect has no place.
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

// The rule holds of an interconnect port inside the module declaring it, and
// in an interface and a generate block, of an interconnect the block declares
// and of one its module does.
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

}  // namespace
