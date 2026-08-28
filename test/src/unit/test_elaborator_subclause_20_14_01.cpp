#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §20.14.1: the seed argument of $random shall be an integral variable. An
// integer seed satisfies the rule and elaborates cleanly.
TEST(RandomSeedType, IntegralSeedIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.14.1: a 2-state `int` is an integral type, so it is an acceptable seed —
// a different integral declaration than `integer`, taking the same accept path.
TEST(RandomSeedType, IntSeedIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.14.1: a packed vector is integral, so a `bit [31:0]` seed is accepted.
TEST(RandomSeedType, PackedVectorSeedIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  bit [31:0] seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.14.1: a narrow `byte` is likewise integral and is an acceptable seed.
TEST(RandomSeedType, ByteSeedIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  byte seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.14.1: a real seed is not an integral variable and is rejected.
TEST(RandomSeedType, RealSeedIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  real seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "seed argument of $random shall be an integral variable", 4, "20.14.1"));
}

// §20.14.1: a shortreal seed is a real (non-integral) type and is rejected.
TEST(RandomSeedType, ShortrealSeedIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  shortreal seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "seed argument of $random shall be an integral variable", 4, "20.14.1"));
}

// §20.14.1: a realtime seed is also a real type, not integral, and is rejected.
TEST(RandomSeedType, RealtimeSeedIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  realtime seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "seed argument of $random shall be an integral variable", 4, "20.14.1"));
}

// §20.14.1: a string seed is likewise non-integral and rejected.
TEST(RandomSeedType, StringSeedIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  string seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "seed argument of $random shall be an integral variable", 4, "20.14.1"));
}

// §20.14.1: the seedless form takes no argument, so it never triggers the
// integral-seed check.
TEST(RandomSeedType, SeedlessFormIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer x;\n"
      "  initial x = $random;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.14.1 requires the seed argument of $random to be an integral variable and
// puts no condition on where the call is written, so every position a statement
// holds a statement in is a position the report is made at. CheckRandomSeedStmt
// in src/elaborator/elaborator_validate_matches.cpp had written out eight of
// the thirteen child-statement links Stmt declares, and now takes the list from
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h. The cases
// below cover one newly reached position each.

// Stmt::for_steps holds a for loop's step assignments, a member of its own
// beside the initializers the walk already reached.
TEST(RandomSeedType, RealSeedInAForStepIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  real seed;\n"
      "  integer x;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 2; x = $random(seed)) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "seed argument of $random shall be an integral variable", 5, "20.14.1"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
TEST(RandomSeedType, RealSeedInAnAssertionPassStatementIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  real seed;\n"
      "  integer x;\n"
      "  logic ok;\n"
      "  initial assert (ok) x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "seed argument of $random shall be an integral variable", 5, "20.14.1"));
}

TEST(RandomSeedType, RealSeedInAnAssertionFailStatementIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  real seed;\n"
      "  integer x;\n"
      "  logic ok;\n"
      "  initial assert (ok) else x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "seed argument of $random shall be an integral variable", 5, "20.14.1"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, kept in
// Stmt::randcase_items. §20.14.1 is a rule about the source, so it holds
// whether the weighted draw would select the item or not.
TEST(RandomSeedType, RealSeedInARandcaseItemIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  real seed;\n"
      "  integer x;\n"
      "  initial randcase 1: x = $random(seed); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "seed argument of $random shall be an integral variable", 4, "20.14.1"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(RandomSeedType, RealSeedInARandsequenceCodeBlockIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  real seed;\n"
      "  integer x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = $random(seed); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "seed argument of $random shall be an integral variable", 6, "20.14.1"));
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second list under
// Stmt::rs_productions, so a walk reaches it without reaching
// RsProd::code_stmts and the case above does not answer for it.
TEST(RandomSeedType, RealSeedInARandsequenceWeightCodeBlockIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  real seed;\n"
      "  integer x;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { x = $random(seed); };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "seed argument of $random shall be an integral variable", 7, "20.14.1"));
}

}  // namespace
