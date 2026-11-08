#include <gtest/gtest.h>

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

TEST(DpiDeclElab, AClassTypedImportFormalIsError) {
  ElabFixture f;
  Elaborate(R"(
    class C;
      int x;
    endclass
    module m;
      import "DPI-C" function void take(input C handle);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "formal argument 'handle' has a class type, which cannot be passed "
      "through the DPI",
      6, "35.5.4"));
}

TEST(DpiDeclElab, AClassTypedImportResultIsError) {
  ElabFixture f;
  Elaborate(R"(
    class C;
      int x;
    endclass
    module m;
      import "DPI-C" function C make();
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "imported function 'make' has a class type as its result, which cannot "
      "be passed through the DPI",
      6, "35.5.5"));
}

TEST(DpiDeclElab, AClassTypedExportFormalIsError) {
  ElabFixture f;
  Elaborate(R"(
    class C;
      int x;
    endclass
    module m;
      export "DPI-C" function give;
      function void give(input C handle);
      endfunction
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "has a formal argument 'handle' of a class type, which cannot be passed "
      "through the DPI",
      6, "35.5.4"));
}

TEST(DpiDeclElab, ATypedefOfAPermittedTypeStaysPermitted) {
  ElabFixture f;
  Elaborate(R"(
    typedef int my_int_t;
    module m;
      import "DPI-C" function void take(input my_int_t v);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DpiDeclElab, FormalsDifferingOnlyInSigningDisagree) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function void sv_f(input int x);
    endmodule
    module n;
      import "DPI-C" function void sv_f(input int unsigned x);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI declaration of linkage name 'sv_f' "
                            "disagrees with the earlier declaration's type "
                            "signature",
                            6, "35.5.4"));
}

TEST(DpiDeclElab, ResultsDifferingOnlyInSigningDisagree) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int sv_r();
    endmodule
    module n;
      import "DPI-C" function int unsigned sv_r();
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI declaration of linkage name 'sv_r' "
                            "disagrees with the earlier declaration's type "
                            "signature",
                            6, "35.5.4"));
}

TEST(DpiDeclElab, OneSigningSpelledTwoWaysAgrees) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function void sv_s(input int x);
    endmodule
    module n;
      import "DPI-C" function void sv_s(input int signed x);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DpiDeclElab, ATypedefAgreesWithTheTypeItNames) {
  ElabFixture f;
  Elaborate(R"(
    typedef int my_int_t;
    module m;
      import "DPI-C" function void sv_t(input my_int_t x);
    endmodule
    module n;
      import "DPI-C" function void sv_t(input int x);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DpiDeclElab, TypedefsOfDifferentTypesDisagree) {
  ElabFixture f;
  Elaborate(R"(
    typedef int my_int_t;
    typedef real my_real_t;
    module m;
      import "DPI-C" function void sv_u(input my_int_t x);
    endmodule
    module n;
      import "DPI-C" function void sv_u(input my_real_t x);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI declaration of linkage name 'sv_u' "
                            "disagrees with the earlier declaration's type "
                            "signature",
                            8, "35.5.4"));
}

TEST(DpiDeclElab, OneUnresolvedNameOnBothSidesAgrees) {
  ElabFixture f;
  Elaborate(R"(
    module m #(parameter type T = int);
      import "DPI-C" function void sv_v(input T x);
    endmodule
    module n #(parameter type T = int);
      import "DPI-C" function void sv_v(input T x);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DpiDeclElab, AnImportTakingANativeFunctionsNameIsARedeclaration) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function int sv_g(); return 1; endfunction
      import "DPI-C" function int sv_g();
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "redeclaration of 'sv_g'", 4,
                            "23.9"));
}

TEST(DpiDeclElab, AnImportTakingAVariablesNameIsARedeclaration) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      logic sv_h;
      import "DPI-C" function void sv_h();
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "redeclaration of 'sv_h'", 4,
                            "23.9"));
}

TEST(DpiDeclElab, TwoImportsOfOneNameDrawOneReport) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function void sv_k();
      import "DPI-C" function void sv_k();
    endmodule
  )",
            f, "m");
  EXPECT_EQ(f.diag.ErrorCount(), 1U);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI import name 'sv_k' already declared in this "
                            "scope",
                            4, "35.5.4"));
}

}  // namespace
