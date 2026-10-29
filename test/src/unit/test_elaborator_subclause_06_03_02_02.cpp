// §6.3.2.2 Drive strength: the drive strength specification lets the statement
// that declares a net also place a continuous assignment on it. §6.3.2 states
// the same thing as the restriction it is -- drive strength is used only where
// the net's declaring statement also places a continuous assignment on it -- so
// a declaration carrying a strength and no assignment is what the rule rejects.
//
// The plain pair, one net declared with a strength and one without an
// assignment beside it, is covered under §6.3.2, where the restriction is
// stated. What is left to this file is where the rule reaches: it belongs to
// the declaration, not to the statement and not to the module's own item list,
// and the cases below are the ones that tell those three readings apart. A
// declarator sharing a statement with an assigned one, and a declaration
// inside a generate block, are both places a coarser check reports nothing.
//
// Every source drives strength0 and strength1 to different values (weak0 is 2,
// pull1 is 3) so that neither field can stand in for the other.
//
// The report the rejections read back carries Subclause("6.3.2"), the
// subclause that states the restriction, because §6.3.2.2 states none of its
// own.

#include <gtest/gtest.h>

#include <cstdint>
#include <format>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The statement does place a continuous assignment -- on `a`. It places none
// on `b`, which carries the same strength, and the rule speaks of the net the
// statement declares rather than of the statement. The report names §6.3.2,
// which states the restriction; §6.3.2.2 states only the permission.
TEST(NetDeclDriveStrength, DeclaratorSharingAnAssignedStatementIsRejected) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  wire (pull1, weak0) a = 1'b1, b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength on net declaration requires an assignment", 2, "6.3.2"));
}

// The rule reaches a declaration inside a selected generate block, and the
// report there names §6.3.2 like the one beside the module's own items.
TEST(NetDeclDriveStrength, GenerateBlockNetWithoutAssignmentIsRejected) {
  ElabFixture f;
  ElabOk(
      "module m #(parameter N = 1) ();\n"
      "  generate\n"
      "    if (N == 1) begin : g\n"
      "      wire (pull1, weak0) w;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength on net declaration requires an assignment", 4, "6.3.2"));
}

// The counterpart to the case above. Without it, a check that rejected every
// strength inside a generate block -- or one that rejected the whole construct
// for an unrelated reason -- would report the same failure and read as
// coverage of the rule.
TEST(NetDeclDriveStrength, GenerateBlockNetCarryingItsAssignmentIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module m #(parameter N = 1) ();\n"
             "  generate\n"
             "    if (N == 1) begin : g\n"
             "      wire (pull1, weak0) w = 1'b1;\n"
             "    end\n"
             "  endgenerate\n"
             "endmodule\n"));
}

// §27.5: a generate block the condition does not select is not elaborated, so
// the declaration inside it never exists and there is no net for §6.3.2.2 to
// speak about. This is the case that separates the rule as elaborated from the
// rule as a walk over the syntax tree, which would reach both branches and
// reject a design the standard accepts.
TEST(NetDeclDriveStrength, UnselectedGenerateBranchIsNotHeldToTheRule) {
  EXPECT_TRUE(
      ElabOk("module m #(parameter N = 1) ();\n"
             "  generate\n"
             "    if (N == 0) begin : g\n"
             "      wire (pull1, weak0) w;\n"
             "    end\n"
             "  endgenerate\n"
             "endmodule\n"));
}

constexpr const char* kStrengthNeedsAssignment =
    "drive strength on net declaration requires an assignment";

// The rule speaks of a net declaration whatever its net type, so each built-in
// type that takes a drive strength is reported without an assignment and
// accepted with one. A trireg reaches the drive strength only after reading no
// charge strength, a path of its own through the parser.
TEST(NetDeclDriveStrength, EveryNetTypeIsHeldToTheRule) {
  for (const char* net_type : {"tri", "wand", "wor", "triand", "trior", "tri0",
                               "tri1", "uwire", "trireg"}) {
    ElabFixture f;
    ElabOk(
        std::format("module m;\n  {} (pull1, weak0) w;\nendmodule\n", net_type),
        f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kStrengthNeedsAssignment, 2,
                              "6.3.2"))
        << net_type;
    EXPECT_TRUE(ElabOk(std::format(
        "module m;\n  {} (pull1, weak0) w = 1'b1;\nendmodule\n", net_type)))
        << net_type;
  }
}

// A vector declared with a drive strength is held to the rule like a scalar.
TEST(NetDeclDriveStrength, VectorNetIsHeldToTheRule) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  tri (pull0, pull1) [7:0] v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kStrengthNeedsAssignment, 2,
                            "6.3.2"));
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  tri (pull0, pull1) [7:0] v = 8'h5a;\n"
             "endmodule\n"));
}

// The declaration is held to the rule in an interface's body, a program's and
// a nested module's, each elaborated through its instance. A checker, a class
// and a subroutine declare no nets, so the rule has no case there.
TEST(NetDeclDriveStrength, EveryInstantiatedScopeIsHeldToTheRule) {
  struct Place {
    const char* before;
    const char* after;
    uint32_t line;
  };
  for (const Place& p : {
           Place{"interface i;\n",
                 "endinterface\nmodule m;\n  i u();\nendmodule\n", 2},
           Place{"program p;\n", "endprogram\nmodule m;\n  p u();\nendmodule\n",
                 2},
           Place{"module m;\n  module inner;\n",
                 "  endmodule\n  inner u();\nendmodule\n", 3},
       }) {
    ElabFixture f;
    ElabOk(std::format("{}  wire (pull1, weak0) w;\n{}", p.before, p.after), f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kStrengthNeedsAssignment,
                              p.line, "6.3.2"))
        << p.before;
    EXPECT_TRUE(ElabOk(std::format("{}  wire (pull1, weak0) w = 1'b1;\n{}",
                                   p.before, p.after)))
        << p.before;
  }
}

// A net of the compilation unit is held to the rule as well, though no module
// elaborates it. Its nearest allowed form differs: §3.12.1 keeps a net
// declaration assignment out of the unit, so the strength's assignment is
// reported under that rule alone and the strength itself is not.
TEST(NetDeclDriveStrength, CompilationUnitNetIsHeldToTheRule) {
  ElabFixture bare;
  ElabOk(
      "wire (pull1, weak0) w;\n"
      "module m;\n"
      "endmodule\n",
      bare);
  EXPECT_TRUE(ReportedError(bare.diag.Diagnostics(), kStrengthNeedsAssignment,
                            1, "6.3.2"));
  ElabFixture assigned;
  ElabOk(
      "wire (pull1, weak0) w = 1'b1;\n"
      "module m;\n"
      "endmodule\n",
      assigned);
  EXPECT_FALSE(ReportedError(assigned.diag.Diagnostics(),
                             kStrengthNeedsAssignment, 1, "6.3.2"));
  EXPECT_TRUE(ReportedError(assigned.diag.Diagnostics(),
                            "a net declaration with an implicit continuous "
                            "assignment cannot stand in the compilation-unit "
                            "scope",
                            1, "3.12.1"));
  EXPECT_TRUE(
      ElabOk("wire w;\n"
             "module m;\n"
             "endmodule\n"));
}

// A package's net is held to the rule as well, and like the unit's it is
// reached without a module: §26.2 keeps a net declaration assignment out of a
// package, so there too the assignment is reported under that rule alone.
TEST(NetDeclDriveStrength, PackageNetIsHeldToTheRule) {
  ElabFixture bare;
  ElabOk(
      "package p;\n"
      "  wire (pull1, weak0) w;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      bare);
  EXPECT_TRUE(ReportedError(bare.diag.Diagnostics(), kStrengthNeedsAssignment,
                            2, "6.3.2"));
  ElabFixture assigned;
  ElabOk(
      "package p;\n"
      "  wire (pull1, weak0) w = 1'b1;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      assigned);
  EXPECT_FALSE(ReportedError(assigned.diag.Diagnostics(),
                             kStrengthNeedsAssignment, 2, "6.3.2"));
  EXPECT_TRUE(ReportedError(assigned.diag.Diagnostics(),
                            "net declaration with implicit continuous "
                            "assignment is not allowed in a package",
                            2, "26.2"));
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  wire w;\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
