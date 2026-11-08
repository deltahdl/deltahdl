#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DpiGlobalNameElab, DuplicateDefaultExportLinkageInSameScopeIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      export "DPI-C" function sv_same;
      export "DPI-C" function sv_same;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export linkage name 'sv_same' already "
                            "declared in this scope",
                            4, "35.4"));
}

TEST(DpiGlobalNameElab, SameExportLinkageAcrossDifferentScopesIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function int sv_a(input int x);
      endfunction
      export "DPI-C" link = function sv_a;
    endmodule
    module n;
      function int sv_b(input int x);
      endfunction
      export "DPI-C" link = function sv_b;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiGlobalNameElab, ImportExportSameLinkageDifferentVersionStringIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function int f(input int x);
    endmodule
    module n;
      export "DPI" link = function sv_g;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI linkage name 'link' was previously declared "
                            "with version string",
                            6, "35.4"));
}

TEST(DpiGlobalNameElab,
     ExportsSharingLinkageWithMismatchedFunctionSignaturesIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function int sv_a(input int x);
      endfunction
      export "DPI-C" link = function sv_a;
    endmodule
    module n;
      function bit sv_b(input int x);
      endfunction
      export "DPI-C" link = function sv_b;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export linkage name 'link' was previously "
                            "declared with a different type signature",
                            10, "35.4"));
}

TEST(DpiGlobalNameElab, ExportsSharingLinkageWithMatchingTaskSignaturesIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      task sv_t;
      endtask
      export "DPI-C" link = task sv_t;
    endmodule
    module n;
      task sv_u;
      endtask
      export "DPI-C" link = task sv_u;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiGlobalNameElab, ImportExportSameLinkageSameVersionStringIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function int f(input int x);
    endmodule
    module n;
      function int sv_g(input int x);
      endfunction
      export "DPI-C" link = function sv_g;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiGlobalNameElab, DuplicateExportLinkageInOnePackageIsError) {
  ElabFixture f;
  Elaborate(R"(
    package p;
      function int sv_a(input int x);
      endfunction
      function int sv_b(input int x);
      endfunction
      export "DPI-C" link = function sv_a;
      export "DPI-C" link = function sv_b;
    endpackage
    module m;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export linkage name 'link' already declared "
                            "in this scope",
                            8, "35.4"));
}

TEST(DpiGlobalNameElab, PackageAndModuleExportsOfOneLinkageAreDifferentScopes) {
  ElabFixture f;
  Elaborate(R"(
    package p;
      function int sv_a(input int x);
      endfunction
      export "DPI-C" link = function sv_a;
    endpackage
    module m;
      function int sv_b(input int x);
      endfunction
      export "DPI-C" link = function sv_b;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiGlobalNameElab, APackageDeclarationJoinsTheVersionStringAgreement) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function int f(input int x);
    endmodule
    package p;
      import "DPI" link = function int g(input int x);
    endpackage
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI linkage name 'link' was previously declared "
                            "with version string",
                            6, "35.4"));
}

TEST(DpiGlobalNameElab,
     ACompilationUnitDeclarationJoinsTheVersionStringAgreement) {
  ElabFixture f;
  Elaborate(R"(
    import "DPI" link = function int g(input int x);
    module m;
      import "DPI-C" link = function int f(input int x);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI linkage name 'link' was previously declared "
                            "with version string",
                            2, "35.4"));
}

TEST(DpiGlobalNameElab, DuplicateExportLinkageInAGenerateBlockIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      if (1) begin : g
        function int sv_a(input int x);
        endfunction
        function int sv_b(input int x);
        endfunction
        export "DPI-C" link = function sv_a;
        export "DPI-C" link = function sv_b;
      end
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export linkage name 'link' already "
                            "declared in this scope",
                            9, "35.4"));
}

TEST(DpiGlobalNameElab, ExportLinkageInAGenerateBlockIsItsOwnScope) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function int sv_a(input int x);
      endfunction
      export "DPI-C" link = function sv_a;
      if (1) begin : g
        function int sv_b(input int x);
        endfunction
        export "DPI-C" link = function sv_b;
      end
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DpiGlobalNameElab, ExportsDifferingOnlyInSigningAreError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_a(input int x);
      endfunction
      export "DPI-C" link_s = function sv_a;
    endmodule
    module n;
      function void sv_b(input int unsigned x);
      endfunction
      export "DPI-C" link_s = function sv_b;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export linkage name 'link_s' was previously "
                            "declared with a different type signature",
                            10, "35.4"));
}

TEST(DpiGlobalNameElab, ExportsWithATypedefOfTheSameTypeAgree) {
  ElabFixture f;
  Elaborate(R"(
    typedef int my_int_t;
    module m;
      function void sv_a(input my_int_t x);
      endfunction
      export "DPI-C" link_t = function sv_a;
    endmodule
    module n;
      function void sv_b(input int x);
      endfunction
      export "DPI-C" link_t = function sv_b;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
