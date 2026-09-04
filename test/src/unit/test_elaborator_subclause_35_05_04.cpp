#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DpiDeclElab, DuplicateImportNameInSameModuleIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int foo(input int a);
      import "DPI-C" function int foo(input int a);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "DPI import name 'foo' already declared in this scope", 4, "35.5.4"));
}

TEST(DpiDeclElab, DistinctImportNamesInSameModuleOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int foo(input int a);
      import "DPI-C" function int bar(input int a);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiDeclElab, SameImportNameInDifferentModulesOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int foo(input int a);
    endmodule
    module n;
      import "DPI-C" function int foo(input int a);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiDeclElab, SignatureMismatchAcrossModulesByDefaultLinkageIsError) {
  // §35.5.4: when no c_identifier is given, the linkage name defaults to the
  // SystemVerilog name. Two declarations sharing that linkage must agree.
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int foo(input int a);
    endmodule
    module n;
      import "DPI-C" function int foo(input int a, input int b);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI declaration of linkage name 'foo' disagrees "
                            "with the earlier declaration's type signature",
                            6, "35.5.4"));
}

TEST(DpiDeclElab, SignatureMismatchOnExplicitLinkageIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" my_link = function int sv_a(input int x);
    endmodule
    module n;
      import "DPI-C" my_link = function int sv_b(input bit x);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI declaration of linkage name 'my_link' "
                            "disagrees with the earlier declaration's type "
                            "signature",
                            6, "35.5.4"));
}

TEST(DpiDeclElab, PureVsContextDifferenceUnderSameLinkageIsError) {
  // §35.5.4 includes the pure/context qualifiers in the type signature.
  // The qualifier precedes the c_identifier: §35.5.4 gives
  // `import "DPI-C" pure function real sin(real);` and
  // `import "DPI-C" newQueue=function chandle newAnonQueue(...);` on printed
  // page 978, and Parser::ParseDpiImport in src/parser/parser_dpi.cpp reads
  // pure/context before ParserDpiHelpers::TryParseDpiCName. Written the other
  // way round the source does not parse, and the signature rule is never
  // reached.
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" pure link = function int f(input int x);
    endmodule
    module n;
      import "DPI-C" context link = function int g(input int x);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI declaration of linkage name 'link' disagrees "
                            "with the earlier declaration's type signature",
                            6, "35.5.4"));
}

TEST(DpiDeclElab, MatchingSignatureUnderSameLinkageOk) {
  // The two declarations agree in every component the signature holds, and
  // they differ in the one thing outside it: the name of the formal, 'x' in
  // one and 'y' in the other. §35.5.4 licenses exactly that difference: "It is
  // permitted to have multiple declarations of the same imported or exported
  // subroutine in different scopes; therefore, argument names and default
  // values can vary, provided the type compatibility constraints are met."
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function int f(input int x);
    endmodule
    module n;
      import "DPI-C" link = function int g(input int y);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

// §35.5.4: "It is permitted to have multiple declarations of the same imported
// or exported subroutine in different scopes; therefore, argument names and
// default values can vary, provided the type compatibility constraints are
// met." A default value is no part of the type signature the clause
// enumerates, so two declarations differing in nothing else are both accepted.
TEST(DpiDeclElab, DifferingDefaultValuesUnderSameLinkageOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function int f(input int x = 1);
    endmodule
    module n;
      import "DPI-C" link = function int g(input int x = 2);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiDeclElab, SignatureReturnTypeMismatchUnderSameLinkageIsError) {
  // The shared-linkage signature comparison includes the return type.
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function int f(input int x);
    endmodule
    module n;
      import "DPI-C" link = function bit g(input int x);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI declaration of linkage name 'link' disagrees "
                            "with the earlier declaration's type signature",
                            6, "35.5.4"));
}

TEST(DpiDeclElab, SignatureSpecStringMismatchUnderSameLinkageIsError) {
  // The signature also includes the dpi_spec_string ("DPI-C" vs "DPI").
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function int f(input int x);
    endmodule
    module n;
      import "DPI" link = function int g(input int x);
    endmodule
  )",
            f, "m");
  // The "DPI" spec string also draws the §35.4 version-string error and the
  // §35.5.4 deprecation warning; the §35.5.4 signature error is the one here.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI declaration of linkage name 'link' disagrees "
                            "with the earlier declaration's type signature",
                            6, "35.5.4"));
}

TEST(DpiDeclElab, SignatureArgDirectionMismatchUnderSameLinkageIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function void f(input int x);
    endmodule
    module n;
      import "DPI-C" link = function void g(output int x);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI declaration of linkage name 'link' disagrees "
                            "with the earlier declaration's type signature",
                            6, "35.5.4"));
}

// §35.5.4: "The type includes dimensions and bounds of any arrays or array
// dimensions." Two packed dimensions of different widths are two types, and
// the declarations below agree in every other component of the signature, so
// the packed bounds are what this rejection rests on.
TEST(DpiDeclElab, SignaturePackedBoundsMismatchUnderSameLinkageIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function int f(input bit [7:0] a);
    endmodule
    module n;
      import "DPI-C" link = function int g(input bit [15:0] a);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI declaration of linkage name 'link' disagrees "
                            "with the earlier declaration's type signature",
                            6, "35.5.4"));
}

// §35.5.4: "The type includes dimensions and bounds of any arrays or array
// dimensions." The sentence names the bounds and not the width, so [0:7] and
// [7:0] are two types although each is eight bits wide.
TEST(DpiDeclElab, SignaturePackedBoundsReversedUnderSameLinkageIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function int f(input bit [0:7] a);
    endmodule
    module n;
      import "DPI-C" link = function int g(input bit [7:0] a);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI declaration of linkage name 'link' disagrees "
                            "with the earlier declaration's type signature",
                            6, "35.5.4"));
}

// §35.5.4: "The type includes dimensions and bounds of any arrays or array
// dimensions", which says the same of an unpacked dimension as of a packed
// one. The two formals below are both arrays of int and differ in the bounds
// alone.
TEST(DpiDeclElab, SignatureUnpackedBoundsMismatchUnderSameLinkageIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function int f(input int a [0:3]);
    endmodule
    module n;
      import "DPI-C" link = function int g(input int a [0:7]);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI declaration of linkage name 'link' disagrees "
                            "with the earlier declaration's type signature",
                            6, "35.5.4"));
}

// §35.5.4 makes the bounds part of the type, and §7.4.1 writes each of them as
// a constant_expression -- "Each packed dimension in a packed array
// declaration shall be specified by a range specification of the form [
// constant_expression : constant_expression ]" -- so a bound is the value its
// expression evaluates to and not the text it was written with. [3+4:0] and
// [7:0] are one type, and the two declarations agree.
TEST(DpiDeclElab, SignaturePackedBoundsAgreeingAfterFoldingUnderSameLinkageOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function int f(input bit [7:0] a);
    endmodule
    module n;
      import "DPI-C" link = function int g(input bit [3+4:0] a);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

// §35.5.4: "The signature includes the return type and the number, order,
// direction, and types of each and every argument." The two declarations below
// give the same two arguments in opposite order, and the arguments differ in
// their direction and in their type, which are what the signature records of
// an argument. The order is therefore the only thing left between them.
TEST(DpiDeclElab, SignatureArgOrderMismatchUnderSameLinkageIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function void f(input int a, output bit b);
    endmodule
    module n;
      import "DPI-C" link = function void g(output bit b, input int a);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI declaration of linkage name 'link' disagrees "
                            "with the earlier declaration's type signature",
                            6, "35.5.4"));
}

// §35.5.4: "For any given c_identifier ..., all declarations, regardless of
// scope, shall have exactly the same type signature." A package body is one
// such scope — A.1.11 makes dpi_import_export a package_item — so an import
// declared there is compared against the declarations of its linkage name in
// every other scope.
TEST(DpiDeclElab, APackageImportJoinsTheSignatureAgreementForItsLinkageName) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function int f(input int x);
    endmodule
    package p;
      import "DPI-C" link = function int g(input bit x);
    endpackage
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI declaration of linkage name 'link' disagrees "
                            "with the earlier declaration's type signature",
                            6, "35.5.4"));
}

// §35.5.4: "multiple imports of the same subroutine name into the same scope
// are forbidden." The scope a package body makes is one scope for that rule.
TEST(DpiDeclElab, DuplicateImportNameInOnePackageIsError) {
  ElabFixture f;
  Elaborate(R"(
    package p;
      import "DPI-C" a = function int dup(input int x);
      import "DPI-C" b = function int dup(input int x);
    endpackage
    module m;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI import name 'dup' already declared in this "
                            "scope",
                            4, "35.5.4"));
}

}  // namespace
