#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

// §26.3 rules on printed page 809 that the import declaration "provides direct
// visibility of identifiers within packages" and "allows identifiers declared
// within packages to be visible within the current scope without a package name
// qualifier", and puts no condition on the statement the reference stands in. A
// bare read that neither the module nor an imported package supplies therefore
// names nothing, which Elaborator::ValidateUnresolvedReferences reports through
// ReportUnresolvedRefs in src/elaborator/elaborator_scope_rules.cpp as
// "reference to unresolved identifier" under §23.9 --
// PackageImport.UnresolvedReferenceIsError in
// test/src/unit/test_elaborator_subclause_26_03a.cpp is that report for a read
// written directly in an initial procedure.
//
// CollectProcRhsIdents in src/elaborator/elaborator_scope_rules_names.cpp
// collects the reads that report judges, and it had written out nine of the
// thirteen child-statement links Stmt declares. It now takes the list from
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h, and the
// five cases below cover one newly reached position each:
// Stmt::assert_pass_stmt, Stmt::assert_fail_stmt, the body of a randcase item,
// and the two statement lists Stmt::rs_productions holds, which
// ForEachRandsequenceRuleStmt reaches by different members --
// RsProd::code_stmts and RsRule::weight_code -- so each is its own position.
//
// The omission cost a report not made: a read of an undeclared name in one of
// those five positions was never collected, so the source elaborated clean. The
// accepting counterparts, which show that a declaration in the same newly
// reached position still answers for the read, stand in
// test/src/unit/test_elaborator_subclause_06_05b.cpp.
//
// The module wildcard-imports `pkg` so that the read is judged against the
// import and not merely against the module: `pkg` declares `supplied` and does
// not declare `absent`, so §26.3 makes nothing visible under that name and the
// report stands.
//
// `stmt` is written at line 8 and may run to several lines, so the line the
// report stands at is read back out of the source rather than counted.
void ExpectUnresolvedProcReadIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "package pkg;\n  int supplied;\nendpackage\n"
      "module m;\n  import pkg::*;\n  int r;\n  initial\n    " +
      stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'absent'",
                            LineHolding(src, "r = absent;"), "23.9"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// which the parser keeps in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt.
// This case and the next cover one arm each.
TEST(PackageImport, UnresolvedProcReadInAnAssertionPassStmt) {
  ExpectUnresolvedProcReadIn("assert (r) r = absent;");
}

TEST(PackageImport, UnresolvedProcReadInAnAssertionFailStmt) {
  ExpectUnresolvedProcReadIn("assert (r) else r = absent;");
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §26.3 is a rule about the source, so it holds whether the weighted
// draw would select the item or not.
TEST(PackageImport, UnresolvedProcReadInARandcaseItem) {
  ExpectUnresolvedProcReadIn("randcase 1: r = absent; endcase");
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(PackageImport, UnresolvedProcReadInARandsequenceCodeBlock) {
  ExpectUnresolvedProcReadIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { r = absent; };\n"
      "      endsequence\n"
      "    end");
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second list under
// Stmt::rs_productions, so a walk reaches it without reaching
// RsProd::code_stmts and the case above does not answer for it.
TEST(PackageImport, UnresolvedProcReadInARandsequenceWeightCodeBlock) {
  ExpectUnresolvedProcReadIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { r = absent; };\n"
      "        alt : { r = 1; };\n"
      "      endsequence\n"
      "    end");
}

}  // namespace
