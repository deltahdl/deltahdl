

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

namespace {

TEST(PackageImport, MultiplePackages) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef int t1;\n"
             "endpackage\n"
             "package p2;\n"
             "  typedef int t2;\n"
             "endpackage\n"
             "module m;\n"
             "  import p1::*;\n"
             "  import p2::*;\n"
             "endmodule\n"));
}

TEST(PackageImport, WildcardImportedIntoModule) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "  byte_t data;\n"
             "endmodule\n"));
}

TEST(PackageImport, WildcardImportFunctionIntoModule) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  function int add(int a, int b); return a + b; endfunction\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageImport, ImportInClassScopeError) {
  ElabFixture f;
  // The rule is reported while parsing the class body, so the source does not
  // parse and the permissive helper says that is meant.
  ElaborateSrcAllowingParseErrors(
      "package pkg;\n"
      "  parameter int X = 1;\n"
      "endpackage\n"
      "class c;\n"
      "  import pkg::*;\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package import declaration is not allowed in "
                            "class scope",
                            5, "26.3"));
}

TEST(PackageImport, ImportedIdentifierNotVisibleViaHierarchicalRef) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "endpackage\n"
             "module child;\n"
             "  import pkg::x;\n"
             "endmodule\n"
             "module top;\n"
             "  child c();\n"
             "  int y;\n"
             "  initial y = c.x;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference 'c.x' targets a name "
                            "imported into 'child' from a package",
                            10, "26.3"));
}

TEST(PackageImport, WildcardImportFromUnknownPackageIsError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  import nonexistent_pkg::*;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "import from unknown package 'nonexistent_pkg'", 2,
                            "26.3"));
}

TEST(PackageImport, ExplicitImportFromUnknownPackageIsError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  import nonexistent_pkg::x;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "import from unknown package 'nonexistent_pkg'", 2,
                            "26.3"));
}

TEST(PackageImport, RepeatedExplicitImportFromSamePackageIsAllowed) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  parameter int X = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::X;\n"
             "  import pkg::X;\n"
             "endmodule\n"));
}

TEST(PackageImport, ExplicitImportCollidesWithExistingLocalDeclaration) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  parameter int X = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  int X;\n"
             "  import pkg::X;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "explicit import of 'pkg::X' collides with existing declaration of 'X'",
      6, "26.3"));
}

TEST(PackageImport,
     ExplicitImportCollidesWithExplicitImportFromAnotherPackage) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  parameter int X = 1;\n"
             "endpackage\n"
             "package p2;\n"
             "  parameter int X = 2;\n"
             "endpackage\n"
             "module m;\n"
             "  import p1::X;\n"
             "  import p2::X;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit import of 'p2::X' conflicts with earlier "
                            "explicit import from 'p1'",
                            9, "26.3"));
}

TEST(PackageImport, WildcardAmbiguityBetweenTwoPackagesIsError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  parameter int X = 1;\n"
             "endpackage\n"
             "package p2;\n"
             "  parameter int X = 2;\n"
             "endpackage\n"
             "module m;\n"
             "  int y;\n"
             "  initial y = X;\n"
             "  import p1::*;\n"
             "  import p2::*;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'X' is ambiguous between wildcard "
                            "imports of packages 'p1' and 'p2'",
                            9, "26.3"));
}

TEST(PackageImport, DeclarationAfterWildcardClaimIsError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  parameter int X = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "  int y;\n"
             "  initial y = X;\n"
             "  int X;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of 'X' follows a reference resolved "
                            "through a wildcard package import",
                            8, "26.3"));
}

TEST(PackageImport, LocalDeclShadowsWildcardImportedName) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  parameter int X = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  int X;\n"
             "  import pkg::*;\n"
             "  int y;\n"
             "  initial y = X;\n"
             "endmodule\n"));
}

// §26.3: an explicit import brings in only the symbol it names. Importing
// pkg::A must not make the sibling declaration pkg::B visible unqualified.
TEST(PackageImport, ExplicitImportDoesNotBringSiblingPackageSymbols) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  parameter int A = 1;\n"
             "  parameter int B = 2;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::A;\n"
             "  logic [31:0] y;\n"
             "  initial y = B;\n"
             "endmodule\n",
             f));
  // The §26.3 rule leaves 'B' invisible; the report that fires is the §23.9
  // unresolved bare-identifier read.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'B'", 8,
                            "23.9"));
}

// §26.3: importing an enumeration type by explicit import imports the type name
// only, not the enumeration literals declared inside it. A bare reference to a
// literal of that enum must therefore fail to resolve.
TEST(PackageImport, ExplicitImportOfEnumTypeDoesNotImportLiterals) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package q;\n"
             "  typedef enum { ORIGINAL, FALSE } teeth_t;\n"
             "endpackage\n"
             "module m;\n"
             "  import q::teeth_t;\n"
             "  teeth_t myteeth;\n"
             "  initial myteeth = FALSE;\n"
             "endmodule\n",
             f));
  // The §26.3 rule leaves the literal 'FALSE' invisible; the report that fires
  // is the §23.9 unresolved bare-identifier read.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'FALSE'", 7,
                            "23.9"));
}

// §26.3 (companion to the rule above): "A wildcard import allows all
// identifiers declared within a package to be imported provided the identifier
// is not otherwise defined in the importing scope." The clause's own example
// writes this module as the legal counterpart to the explicit import above,
// commenting `myteeth = FALSE;` as "OK: Direct reference to FALSE refers to the
// FALSE enumeration literal imported from q".
//
// The assertion reads the elaborated design instead of asserting that
// elaboration succeeded. ModuleSkipsUnresolvedCheck in
// src/elaborator/elaborator_scope_rules.cpp returns true for a module carrying
// any wildcard import of a package other than 'std', so
// Elaborator::ValidateUnresolvedReferences skips module 'm' and nothing asks
// whether the bare read of FALSE on line 7 resolves. An acceptance assertion
// here would therefore pass with every path that imports a package's
// enumeration literals deleted.
//
// The value is what makes the claim about FALSE rather than about the vector
// holding two entries: a member read out of a wrongly built vector and a member
// holding its ordinal are told apart only by an ordinal that is not 0, which is
// why the second literal is the one asserted.
//
// Whether the reference then binds to that literal is answered end to end by
// PackageImportSim.WildcardImportEnumLiteralEvaluates in
// test/src/unit/test_simulator_subclause_26_03.cpp, which reads the run-time
// value back. The elaborator does not answer it, and the comment in
// elaborator_scope_rules.cpp says why: a wildcard import can make any name in
// the package locally visible, the module symbol table does not enumerate those
// names, and a bare read therefore cannot be proven unresolved.
TEST(PackageImport, WildcardImportOfEnumBringsLiteralsIntoScope) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package q;\n"
      "  typedef enum { ORIGINAL, FALSE } teeth_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import q::*;\n"
      "  teeth_t myteeth;\n"
      "  initial myteeth = FALSE;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("teeth_t");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 2u);
  EXPECT_EQ(it->second[1].name, "FALSE");
  EXPECT_EQ(it->second[1].value, 1);
}

TEST(PackageScopeReference, PackageScopeParamResolution) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  parameter int WIDTH = 8;\n"
             "endpackage\n"
             "module m;\n"
             "  logic [pkg::WIDTH-1:0] data;\n"
             "endmodule\n"));
}

// §26.3: the package scope resolution operator names any constant member of a
// package. A localparam is a distinct §11.2.1 constant form from a parameter
// and folds through the compound-key path in const evaluation, so exercise it
// in a constant-expression position (a packed range) separately.
TEST(PackageScopeReference, PackageScopeLocalparamResolution) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  localparam int W = 6;\n"
             "endpackage\n"
             "module m;\n"
             "  logic [pkg::W-1:0] data;\n"
             "endmodule\n"));
}

TEST(PackageScopeReference, PackageScopeTypeResolution) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "module m;\n"
             "  pkg::byte_t data;\n"
             "endmodule\n"));
}

TEST(PackageImport, ExplicitImportIdentVisibleUnqualified) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  parameter int WIDTH = 16;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::WIDTH;\n"
             "  logic [WIDTH-1:0] data;\n"
             "endmodule\n"));
}

// A §26.3 package-scoped subroutine call resolves to the function declared in
// the named package, arguments included; the parser file for this subclause
// carries the case that the same call is accepted by the grammar.
TEST(PackageScopeReference, PackageScopedFunctionCallElaborates) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  function int add(int a, int b); return a + b; endfunction\n"
             "endpackage\n"
             "module m;\n"
             "  int x;\n"
             "  initial x = pkg::add(1, 2);\n"
             "endmodule\n"));
}

TEST(PackageImport, FunctionCallBindsToLaterFunctionInSameScope) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int x;\n"
             "  initial x = helper(2);\n"
             "  function int helper(int a); return a + 1; endfunction\n"
             "endmodule\n"));
}

TEST(PackageImport, OuterScopeSearchFindsCompilationUnitName) {
  EXPECT_TRUE(
      ElabOk("localparam int WIDTH = 8;\n"
             "module m;\n"
             "  logic [WIDTH-1:0] data;\n"
             "endmodule\n"));
}

TEST(PackageImport, UnresolvedReferenceIsError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int y;\n"
             "  initial y = nonexistent_identifier;\n"
             "endmodule\n",
             f));
  // A bare read that no import makes visible is reported under §23.9.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier "
                            "'nonexistent_identifier'",
                            3, "23.9"));
}

// §26.3 rules that a wildcard import makes an identifier potentially locally
// visible "at some point within a scope if there is a wildcard import of a
// package before that point within the current scope", and the clause's own
// example on printed page 809 writes both import forms in a module body and
// then declares `teeth_t myteeth;` with the type they made visible. So an
// import in the body carries a package's typedefs and parameters into the
// module, exactly as one in the header does under §26.4.
//
// The four cases below read the elaborated declaration back rather than
// asserting that elaboration succeeded, because nothing reports an unresolved
// named type: EvalTypeWidth at src/elaborator/type_eval.cpp:192 answers 0 for a
// DataTypeKind::kNamed it could not resolve and the run carries on. An
// acceptance assertion therefore holds whether the import was applied or not,
// which is what PackageImport.WildcardImportedIntoModule above still is.
//
// 8 is the width to assert and not 1: RtlirVariable::width defaults to 1, so a
// one-bit declaration cannot tell a resolved type from an untouched field.
TEST(PackageImport, BodyImportedTypedefSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package q;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import q::*;\n"
      "  byte_t data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* data = FindVar(design, "m", "data");
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data->width, 8u);
}

// The explicit form of the same claim. §26.3 states it separately -- "an
// explicit import only imports the symbols specifically referenced by the
// import" -- and the elaborator reaches it through a different branch of
// ApplyImport in src/elaborator/elaborator_module.cpp, so it is asserted
// separately.
TEST(PackageImport, ExplicitBodyImportOfTypedefSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package q;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import q::byte_t;\n"
      "  byte_t data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* data = FindVar(design, "m", "data");
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data->width, 8u);
}

// A package parameter is the other kind of item an import registers, folded
// into the parameter scope rather than the typedef map by RegisterImportItem in
// src/elaborator/elaborator_module.cpp. The declared range is what reads it
// back: RegisterPackageParams in src/elaborator/elaborator_resolve.cpp
// registers 'W' under the qualified key 'q::W' for every package whether it is
// imported or not, so a width of 8 here answers for the unqualified name the
// import is what supplies.
TEST(PackageImport, BodyImportedParameterSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package q;\n"
      "  parameter int W = 8;\n"
      "endpackage\n"
      "module m;\n"
      "  import q::*;\n"
      "  logic [W-1:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* data = FindVar(design, "m", "data");
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data->width, 8u);
}

// The clause's own source, and the declaration the enumeration half of it turns
// on. PackageImport.WildcardImportOfEnumBringsLiteralsIntoScope above reads the
// literals back off mod->enum_types, which RegisterImportedEnumLiterals in
// src/elaborator/elaborator_typedef.cpp fills for a body import already. This
// reads the variable instead: SetEnumTypeInfo in
// src/elaborator/elaborator_decls.cpp looks 'teeth_t' up in the typedef map and
// leaves RtlirVariable::enum_type_name empty on a miss, so nothing in the
// elaborated design recorded that myteeth has an enumeration type at all.
TEST(PackageImport, BodyImportedEnumTypedefNamesTheEnumType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package q;\n"
      "  typedef enum { ORIGINAL, FALSE } teeth_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import q::*;\n"
      "  teeth_t myteeth;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* myteeth = FindVar(design, "m", "myteeth");
  ASSERT_NE(myteeth, nullptr);
  EXPECT_EQ(myteeth->enum_type_name, "teeth_t");
}

// §26.3 makes an identifier potentially locally visible only where "there is a
// wildcard import of a package before that point within the current scope", and
// module 'b' is a scope with no import in it. word_t is declared nowhere 'b'
// can see, so 'b' has to be told nothing about q whatever 'a' imported.
//
// The two widths are one claim each and both are needed. 16 on a's x says the
// import still reaches the module that wrote it, so the test cannot pass by
// importing nothing anywhere. 0 on b's y is what EvalTypeWidth answers for a
// DataTypeKind::kNamed it could not resolve
// (src/elaborator/type_eval.cpp:192), and it is not the 1 that
// RtlirVariable::width defaults to, so it says the declaration was elaborated
// and its type went unresolved rather than that nothing ran.
//
// Both modules have to be elaborated for the question to arise, which is what
// auto_top asks for: with a single named top, 'a' is never elaborated and there
// is nothing for 'b' to inherit.
//
// f.has_errors is deliberately not asserted. §6.18 requires a type identifier
// to be declared, so `word_t y;` in 'b' is illegal and a run that reported it
// would be more correct than this one; nothing in deltahdl reports an
// unresolved named type today, and the width says what the elaborator did
// either way.
TEST(PackageImport, ImportedTypedefDoesNotReachAnotherModule) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "package q;\n"
      "  typedef logic [15:0] word_t;\n"
      "endpackage\n"
      "module a;\n"
      "  import q::*;\n"
      "  word_t x;\n"
      "endmodule\n"
      "module b;\n"
      "  word_t y;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  const auto* x = FindVar(design, "a", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 16u);
  const auto* y = FindVar(design, "b", "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->width, 0u);
}

// The same claim for the parameter an import carries rather than the typedef.
// RegisterImportItem in src/elaborator/elaborator_module.cpp folds an imported
// parameter into the compilation unit's parameter scope, which
// Elaborator::BuildParamScope copies for every module, so this covers the map
// the test above does not.
//
// 1 is what b's y is left at: EvalRangeWidth in src/elaborator/type_eval.cpp
// answers 0 for a bound it cannot fold, and the declared type falls through to
// DataTypeKind::kLogic, which is one bit. It coincides with the default of
// RtlirVariable::width, which is why the ASSERT_NE above it is what says the
// declaration was elaborated at all, and why a's 16 is asserted beside it.
TEST(PackageImport, ImportedParameterDoesNotReachAnotherModule) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "package q;\n"
      "  parameter int W = 16;\n"
      "endpackage\n"
      "module a;\n"
      "  import q::*;\n"
      "  logic [W-1:0] x;\n"
      "endmodule\n"
      "module b;\n"
      "  logic [W-1:0] y;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  const auto* x = FindVar(design, "a", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 16u);
  const auto* y = FindVar(design, "b", "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->width, 1u);
}

// §26.3 (printed page 808): "One way to use declarations made in a package is
// to reference them using the package scope resolution operator ::", written in
// the clause as `ComplexPkg::Complex cout = ComplexPkg::mul(a, b);` -- a
// declaration through a package-qualified type name, with no import in sight.
// The cases above all reach a package typedef through an import, which enters
// it under its bare name, so none of them exercises the prefix itself.
//
// 16 is the width to assert: shortint is the only type in the source, so a
// prefix that resolved to nothing leaves v at 0 and one that resolved to some
// other declaration could not answer 16.
TEST(PackageReference, ScopedTypedefSizesTheVariableWithoutImport) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  typedef shortint word_t;\n"
      "endpackage\n"
      "module m;\n"
      "  pkg::word_t v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* v = FindVar(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 16u);
}

}  // namespace
