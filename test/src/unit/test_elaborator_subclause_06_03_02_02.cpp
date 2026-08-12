// §6.3.2.2 Drive strength: "The drive strength specification allows a
// continuous assignment to be placed on a net in the same statement that
// declares that net." §6.3.2 states the same thing as the restriction it is --
// drive strength "shall only be used when placing a continuous assignment on a
// net in the same statement that declares the net" -- so a declaration
// carrying a strength and no assignment is what the rule rejects.
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

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// The statement does place a continuous assignment -- on `a`. It places none
// on `b`, which carries the same strength, and the rule speaks of the net the
// statement declares rather than of the statement. The report names §6.3.2,
// which states the restriction; §6.3.2.2 states only the permission.
TEST(NetDeclDriveStrength, DeclaratorSharingAnAssignedStatementIsRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  wire (pull1, weak0) a = 1'b1, b;\n"
             "endmodule\n",
             f));
  const delta::Diagnostic* diag =
      FindDiag(f, "drive strength on net declaration requires an assignment");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.3.2");
}

// The rule reaches a declaration inside a selected generate block, and the
// report there names §6.3.2 like the one beside the module's own items.
TEST(NetDeclDriveStrength, GenerateBlockNetWithoutAssignmentIsRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m #(parameter N = 1) ();\n"
             "  generate\n"
             "    if (N == 1) begin : g\n"
             "      wire (pull1, weak0) w;\n"
             "    end\n"
             "  endgenerate\n"
             "endmodule\n",
             f));
  const delta::Diagnostic* diag =
      FindDiag(f, "drive strength on net declaration requires an assignment");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.3.2");
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

}  // namespace
