#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

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

// §26.3 lets a module read a package's declarations through the package scope
// resolution operator, and A.8.4 makes a package-scoped parameter a constant
// primary, so `p::RECURSION` sizes a packed dimension. RegisterPackageParams in
// src/elaborator/elaborator_resolve.cpp folded each package parameter against
// the compilation-unit scope alone, which holds no member of the package's
// enumerations (§6.19), so RECURSION was never recorded under its qualified
// key and the dimension did not fold. The members are (1 << 4), (1 << 5) and
// (1 << 6), whose OR is 112; their ordinals OR to 3.
TEST(PackageScopeReference,
     PackageParameterOverPackageEnumMembersSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef bit [7:0] flag_t;\n"
      "  typedef enum flag_t {\n"
      "    DEEP = (1 << 4), SHALLOW = (1 << 5), REFERENCE = (1 << 6)\n"
      "  } policy_e;\n"
      "  parameter RECURSION = (DEEP | SHALLOW | REFERENCE);\n"
      "endpackage\n"
      "module m;\n"
      "  logic [p::RECURSION-1:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* data = FindVar(design, "m", "data");
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data->width, 112u);
}

// The parameter declared with the enumeration as its type. INITIALIZED is the
// fourth member and carries no value of its own, so §6.19's implicit increment
// gives it 3 and `[p::POST_INIT:0]` four bits.
TEST(PackageScopeReference,
     PackageParameterTypedByAPackageEnumSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef enum {\n"
      "    UNINITIALIZED, PRE_INIT, INITIALIZING, INITIALIZED, ABORTED\n"
      "  } state_e;\n"
      "  parameter state_e POST_INIT = INITIALIZED;\n"
      "endpackage\n"
      "module m;\n"
      "  logic [p::POST_INIT:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* data = FindVar(design, "m", "data");
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data->width, 4u);
}

// A.8.4 writes `[ package_scope ] enum_identifier` as a constant primary of
// its own, so a member is read through the package scope resolution operator
// without a parameter in between. GREEN is 5, so `[p::GREEN:0]` is six bits;
// its ordinal would give two.
TEST(PackageScopeReference, PackageEnumMemberSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef enum { RED = 3, GREEN = 5 } color_t;\n"
      "endpackage\n"
      "module m;\n"
      "  logic [p::GREEN:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* data = FindVar(design, "m", "data");
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data->width, 6u);
}

// The same parameter reached by a wildcard import rather than the operator.
// RegisterImportItem in src/elaborator/elaborator_import.cpp folded the
// imported parameter's initializer again, against a scope holding none of the
// package's enumeration constants under their bare names, so K was left
// unresolved; it now reads the value registration recorded. J reads two of the
// imported literals directly, which Elaborator::BuildParamScope supplies from
// the enumerations RegisterImportedEnumLiterals brought into the module.
TEST(PackageImport, WildcardImportedParameterOverEnumMembersHoldsItsValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef bit [7:0] flag_t;\n"
      "  typedef enum flag_t {\n"
      "    DEEP = (1 << 4), SHALLOW = (1 << 5), REFERENCE = (1 << 6)\n"
      "  } policy_e;\n"
      "  parameter RECURSION = (DEEP | SHALLOW | REFERENCE);\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  localparam int K = RECURSION;\n"
      "  localparam int J = DEEP | REFERENCE;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* k = FindParam(design, "m", "K");
  ASSERT_NE(k, nullptr);
  EXPECT_TRUE(k->is_resolved);
  EXPECT_EQ(k->resolved_value, 112);
  const auto* j = FindParam(design, "m", "J");
  ASSERT_NE(j, nullptr);
  EXPECT_TRUE(j->is_resolved);
  EXPECT_EQ(j->resolved_value, 80);
}

// §6.20.1 lets a package parameter read an earlier one by its bare name, and
// the value the later one is recorded under its qualified key is what a module
// then reads. Registration folded B against the compilation-unit scope, which
// held A only as "p.A", so `p::B` did not fold; the validator alone bound the
// bare name, and only to answer whether B was constant.
TEST(PackageScopeReference,
     PackageParameterReadingAnEarlierOneSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int A = 5;\n"
      "  parameter int B = A + 2;\n"
      "endpackage\n"
      "module m;\n"
      "  logic [p::B-1:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* data = FindVar(design, "m", "data");
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data->width, 7u);
}

}  // namespace
