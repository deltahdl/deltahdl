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

// §26.3 (printed page 809) has an import make a package's identifiers
// visible in the importing scope without the package qualifier, a wildcard
// import every one of them and an explicit import the one it names, and puts
// no condition on the expression the identifier then stands in; so a class the
// package declares serves as the base of a `::` static method call by its bare
// name, as it does qualified. The check that reports an unknown base consulted
// the module's own names and the packages alone, so the wildcard-imported form
// was reported while `p::pk_t::get()` was not.
TEST(PackageScopeReference, WildcardImportedClassIsAScopeBase) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  class pk_t;\n"
      "    static function int get(); return 7; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  int c;\n"
      "  initial c = pk_t::get();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "reference to unresolved package or scope 'pk_t'",
                             9, "26.3"));
}

TEST(PackageScopeReference, ExplicitlyImportedClassIsAScopeBase) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  class pk_t;\n"
      "    static function int get(); return 7; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "  import p::pk_t;\n"
      "  int c;\n"
      "  initial c = pk_t::get();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "reference to unresolved package or scope 'pk_t'",
                             9, "26.3"));
}

// §26.3: an explicit import brings in the one identifier it names, so a class
// of the same package it does not name is no base without the qualifier.
TEST(PackageScopeReference, AClassTheImportDoesNotNameIsNoScopeBase) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  class pk_t;\n"
      "    static function int get(); return 7; endfunction\n"
      "  endclass\n"
      "  class other_t; endclass\n"
      "endpackage\n"
      "module m;\n"
      "  import p::other_t;\n"
      "  int c;\n"
      "  initial c = pk_t::get();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved package or scope 'pk_t'",
                            10, "26.3"));
}

// §3.12.1 makes the compilation-unit scope one the module's upward search
// (§23.9) reaches, and §26.3 (printed page 809) has an import make the
// package's identifiers visible within the scope it is written in; so a
// wildcard import above the module makes a package's localparam readable by
// its bare name inside the module, and its class a `::` base. The uvm-tagged
// sv-tests files import uvm_pkg this way. Both reads were reported, the check
// consulting the module's own imports alone.
TEST(PackageImport, CompilationUnitWildcardImportResolvesABareRead) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  localparam int K = 5;\n"
      "endpackage\n"
      "import p::*;\n"
      "module m;\n"
      "  int c;\n"
      "  initial c = K;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "reference to unresolved identifier 'K'", 7,
                             "23.9"));
}

TEST(PackageImport, CompilationUnitWildcardImportedClassIsAScopeBase) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  class pk_t;\n"
      "    static function int get(); return 7; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "import p::*;\n"
      "module m;\n"
      "  int d;\n"
      "  initial d = pk_t::get();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "reference to unresolved package or scope 'pk_t'",
                             9, "26.3"));
}

// §26.3: an explicit import at compilation-unit scope brings in the one name
// it writes, no other.
TEST(PackageImport, CompilationUnitExplicitImportResolvesItsNameAlone) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  localparam int K = 5;\n"
      "  localparam int L = 6;\n"
      "endpackage\n"
      "import p::K;\n"
      "module m;\n"
      "  int c, d;\n"
      "  initial begin\n"
      "    c = K;\n"
      "    d = L;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "reference to unresolved identifier 'K'", 9,
                             "23.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'L'", 10,
                            "23.9"));
}

// §26.3 has an import make a package's declarations visible in the scope it is
// written in, and §3.12.1 makes the compilation-unit scope the outermost one a
// module's names resolve through, so a package class made visible by a
// wildcard import written outside every module is a class type in a following
// module: `B h;` declares a class variable, and §8.13 lets `h = d` assign a
// subclass handle to it. RegisterImportItem in
// src/elaborator/elaborator_import.cpp entered a package's typedefs and
// parameters into the module's scopes and passed over its classes, so
// ValidateVarDeclTypes never took `h` for a class variable and the assignment
// was reported under §8.4 as a handle assigned to a non-class variable.
TEST(PackageImport, CuScopeWildcardImportedPackageClassIsAClassType) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  class B; int b = 3; endclass\n"
      "endpackage\n"
      "import pk::*;\n"
      "class D extends B; endclass\n"
      "module t;\n"
      "  B h; D d = new;\n"
      "  initial h = d;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "cannot assign class object handle to a non-class variable", 8, "8.4"));
}

// The same through a header import (§26.4) and an explicit import naming the
// class, the two other positions RegisterImportItem serves.
TEST(PackageImport, HeaderWildcardImportedPackageClassIsAClassType) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  class B; int b = 3; endclass\n"
      "endpackage\n"
      "module t import pk::*; ();\n"
      "  class D extends B; endclass\n"
      "  B h; D d = new;\n"
      "  initial h = d;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "cannot assign class object handle to a non-class variable", 7, "8.4"));
}

TEST(PackageImport, ExplicitlyImportedPackageClassIsAClassType) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  class B; int b = 3; endclass\n"
      "endpackage\n"
      "module t;\n"
      "  import pk::B;\n"
      "  class D extends B; endclass\n"
      "  B h; D d = new;\n"
      "  initial h = d;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "cannot assign class object handle to a non-class variable", 8, "8.4"));
}

// A class the explicit import does not name stays out of the module's class
// types, so the report the fix silences is still made for it.
TEST(PackageImport, AClassTheImportDoesNotNameIsNoClassType) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  class B; int b = 3; endclass\n"
      "  class other_t; endclass\n"
      "endpackage\n"
      "module t;\n"
      "  import pk::other_t;\n"
      "  class D; endclass\n"
      "  B h; D d = new;\n"
      "  initial h = d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot assign class object handle to a non-class variable", 9, "8.4"));
}

// §26.3 searches a scope's locally visible identifiers, an explicit import's
// among them, before the candidates a wildcard import supplies (printed page
// 810), so in the clause's top2 module FALSE is q's.
// RegisterImportedEnumLiterals in src/elaborator/elaborator_typedef.cpp emitted
// every literal of p as a module variable, FALSE included, and that variable
// held the name against the import lowering. The literal the explicit import
// names is left to it; TRUE, which no explicit import names, is still emitted,
// and bool_t keeps both members, so a fix that dropped the member from the type
// or the whole type from the module would fail here.
TEST(PackageImport, WildcardLiteralAnExplicitImportNamesIsNotEmitted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef enum { FALSE, TRUE } bool_t;\n"
      "endpackage\n"
      "package q;\n"
      "  typedef enum { ORIGINAL, FALSE } teeth_t;\n"
      "endpackage\n"
      "module top2;\n"
      "  import p::*;\n"
      "  import q::teeth_t, q::ORIGINAL, q::FALSE;\n"
      "  teeth_t myteeth;\n"
      "  initial myteeth = FALSE;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(FindVar(design, "top2", "FALSE"), nullptr);
  EXPECT_NE(FindVar(design, "top2", "TRUE"), nullptr);
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("bool_t");
  ASSERT_NE(it, mod->enum_types.end());
  EXPECT_EQ(it->second.size(), 2u);
}

}  // namespace
