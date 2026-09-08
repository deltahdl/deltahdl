#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

// §6.5 rules on printed page 91 that "Data shall be declared before they are
// used, apart from implicit nets", and two walks in
// src/elaborator/elaborator_scope_rules_names.cpp answer that question of a
// procedural assignment: CollectProcLocalNames gathers the names a procedural
// block declares and CollectProcRhsIdents gathers the names its assignments
// read, and Elaborator::ValidateUnresolvedReferences reports a read that
// neither the block nor the module declares.
//
// Each walk wrote out nine of the thirteen child-statement links Stmt declares,
// and both now take the list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. The four links neither reached
// are Stmt::assert_pass_stmt, Stmt::assert_fail_stmt, the body of a randcase
// item, and the two statement lists Stmt::rs_productions holds --
// RsProd::code_stmts and RsRule::weight_code, which ForEachRandsequenceRuleStmt
// reaches by different members, so each of those is its own position and each
// gets its own case below.
//
// The five cases here cover CollectProcLocalNames, whose omission cost a report
// made wrongly rather than a report not made: a declaration the walk did not
// see is absent from the set of block-local names, so the read of that name
// resolves against nothing and is reported as unresolved under §23.9 although
// §6.5 was satisfied where it stands. Each source declares a variable and reads
// it in one newly reached position, and asserts the source is accepted, so each
// fails if CollectProcRhsIdents is put on the shared list while
// CollectProcLocalNames is left with its own. The rejecting counterparts, one
// per position, stand in test/src/unit/test_elaborator_subclause_26_03b.cpp.
//
// An accepted source produces no report, so there is nothing here for
// ReportedError in lib/cpp/test_helpers/helpers_reported_error.h to name.
//
// `stmt` is the whole statement of the initial procedure and may run to several
// lines. `a` is declared in an unnamed begin-end, which §23.9 lists among the
// elements defining a scope, and `r` is the module variable it is read into.
bool ElaboratesWithBlockLocalIn(const std::string& stmt) {
  return ElabOk("module m;\n  int r;\n  initial\n    " + stmt +
                "\nendmodule\n");
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// which the parser keeps in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt.
// This case and the next cover one arm each.
TEST(NetsAndVariables, BlockLocalReadInAnAssertionPassStmtIsAccepted) {
  EXPECT_TRUE(ElaboratesWithBlockLocalIn("assert (r) begin int a; r = a; end"));
}

TEST(NetsAndVariables, BlockLocalReadInAnAssertionFailStmtIsAccepted) {
  EXPECT_TRUE(
      ElaboratesWithBlockLocalIn("assert (r) else begin int a; r = a; end"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §6.5 is a rule about the source, so the declaration answers for the
// read whether the weighted draw would select the item or not.
TEST(NetsAndVariables, BlockLocalReadInARandcaseItemIsAccepted) {
  EXPECT_TRUE(ElaboratesWithBlockLocalIn(
      "randcase 1: begin int a; r = a; end endcase"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(NetsAndVariables, BlockLocalReadInARandsequenceCodeBlockIsAccepted) {
  EXPECT_TRUE(
      ElaboratesWithBlockLocalIn("begin\n"
                                 "      randsequence(main)\n"
                                 "        main : { begin int a; r = a; end };\n"
                                 "      endsequence\n"
                                 "    end"));
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second list under
// Stmt::rs_productions, so a walk reaches it without reaching
// RsProd::code_stmts and the case above does not answer for it.
TEST(NetsAndVariables, BlockLocalReadInARandsequenceWeightCodeBlockIsAccepted) {
  EXPECT_TRUE(ElaboratesWithBlockLocalIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { begin int a; r = a; end };\n"
      "        alt : { r = 1; };\n"
      "      endsequence\n"
      "    end"));
}

// §23.7 calls `v.f` a dotted name and rules that "the first name component of a
// member select matches a data object", which is what LhsBaseName answers for
// each of the six checks that reduce an lvalue to its base. Its member arm
// followed `base`, a field only a select carries, so it walked off the end of
// every dotted name and answered nothing, and each caller reads nothing as
// "no base to check". §6.5's rule against "a mixture of procedural and
// continuous assignments writing to any term in the expansion of the longest
// static prefix of a variable" is the one that makes that observable: the
// continuous assignment names `v` and the procedural one names a member of it,
// which is a term in the same expansion.
TEST(NetsAndVariables,
     MemberQualifiedProceduralTargetIsAWriteToItsBaseVariable) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic f; } s_t;\n"
      "  s_t v;\n"
      "  logic a, b;\n"
      "  assign v = a;\n"
      "  initial v.f = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'v' has both continuous and procedural "
                            "assignments",
                            5, "6.5"));
}

// §23.7.1: "A name with a package or class scope resolution prefix (::) shall
// always resolve in a downwards manner", so the name before `::` is a package
// or a class rather than a data object, and the walk ends there rather than
// returning it. A net and a package can carry one name, which is what lets this
// case put the two together: descending through the prefix would record `p::x =
// 1` as a procedural write to the net `p` and draw §6.5's net-as-target report
// over a statement that writes no net at all.
TEST(NetsAndVariables, PackageScopedAssignmentIsNotAWriteToThePrefixName) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  int x;\n"
             "endpackage\n"
             "module m;\n"
             "  wire p;\n"
             "  logic a;\n"
             "  assign p = a;\n"
             "  initial p::x = 1;\n"
             "endmodule\n",
             f));
}

}  // namespace
