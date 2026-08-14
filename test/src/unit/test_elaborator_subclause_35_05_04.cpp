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
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = pure function int f(input int x);
    endmodule
    module n;
      import "DPI-C" link = context function int g(input int x);
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

}  // namespace
