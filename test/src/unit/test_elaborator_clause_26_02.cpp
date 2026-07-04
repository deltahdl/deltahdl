#include "fixture_elaborator.h"

namespace {

TEST(PackageDeclarationElaboration,
     NetWithImplicitContinuousAssignmentRejected) {
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  wire w = 1'b0;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageDeclarationElaboration, InitialBlockInPackageRejected) {
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "  initial x = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageDeclarationElaboration, AlwaysBlockInPackageRejected) {
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "  always @(*) x = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageDeclarationElaboration, FinalBlockInPackageRejected) {
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "  final x = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

// §26.2: because a package may hold processes only inside checkers, a
// combinational always procedure sitting directly in the package body is
// rejected, like the general always/initial/final cases above.
TEST(PackageDeclarationElaboration, AlwaysCombBlockInPackageRejected) {
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "  always_comb x = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageDeclarationElaboration, AlwaysFfBlockInPackageRejected) {
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "  logic clk;\n"
             "  always_ff @(posedge clk) x <= 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageDeclarationElaboration, AlwaysLatchBlockInPackageRejected) {
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "  logic en;\n"
             "  always_latch if (en) x = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

// §26.2 explicitly permits populating a package with nets; only a net carrying
// an implicit continuous assignment is barred. A bare net declaration therefore
// elaborates cleanly — the accepting boundary of the rule negated above.
TEST(PackageDeclarationElaboration, NetWithoutContinuousAssignmentAccepted) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  wire w;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageDeclarationElaboration, HierarchicalReferenceFromPackageRejected) {
  EXPECT_FALSE(
      ElabOk("module other;\n"
             "  int hidden;\n"
             "endmodule\n"
             "package pkg;\n"
             "  int leak = other.hidden;\n"
             "endpackage\n"
             "module m;\n"
             "  other o();\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageDeclarationElaboration,
     CompilationUnitScopeReferenceFromPackageRejected) {
  EXPECT_FALSE(
      ElabOk("int cu_scope_var = 7;\n"
             "package pkg;\n"
             "  int leak = cu_scope_var;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageDeclarationElaboration, SingleTimeunitInPackageHeadAccepted) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  timeunit 1ns;\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(PackageDeclarationElaboration,
     TimeunitFollowedByTimeprecisionInPackageHeadAccepted) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ps;\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(PackageDeclarationElaboration, TimeunitsRepeatMatchAccepted) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  timeunit 1ns;\n"
             "  timeunit 1ns;\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(PackageDeclarationElaboration, TimeunitsMismatchRejected) {
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  timeunit 1ns;\n"
             "  timeunit 1ps;\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(PackageDeclarationElaboration, TimeprecisionMismatchRejected) {
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  timeprecision 1ps;\n"
             "  timeprecision 1fs;\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
