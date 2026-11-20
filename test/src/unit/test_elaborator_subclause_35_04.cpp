#include <gtest/gtest.h>

#include <string>
#include <string_view>

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

void ExpectAccepted(const std::string& src, std::string_view top = "m") {
  ElabFixture f;
  Elaborate(src, f, top);
  EXPECT_FALSE(f.diag.HasErrors());
}

void ExpectReport(const std::string& src, const std::string& message, int line,
                  std::string_view top = "m") {
  ElabFixture f;
  Elaborate(src, f, top);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, "35.4"));
}

std::string AlreadyInScope(const char* name) {
  return std::string("DPI export linkage name '") + name +
         "' already declared in this scope";
}

std::string DifferentSignature(const char* name) {
  return std::string("DPI export linkage name '") + name +
         "' was previously declared with a different type signature";
}

std::string DifferentVersionString(const char* name) {
  return std::string("DPI linkage name '") + name +
         "' was previously declared with version string";
}

TEST(DpiGlobalNameElab, ExportedTasksWithEquivalentFormalsShareALinkageName) {
  ExpectAccepted(R"(
    module m;
      task sv_t(input int a); endtask
      export "DPI-C" link = task sv_t;
    endmodule
    module n;
      task sv_u(input int b); endtask
      export "DPI-C" link = task sv_u;
    endmodule
  )");
}

TEST(DpiGlobalNameElab, ExportedTasksWithDifferentFormalsCannotShareALinkage) {
  ExpectReport(R"(
    module m;
      task sv_t(input int a); endtask
      export "DPI-C" link = task sv_t;
    endmodule
    module n;
      task sv_u(input byte b); endtask
      export "DPI-C" link = task sv_u;
    endmodule
  )",
               DifferentSignature("link"), 8);
}

TEST(DpiGlobalNameElab, ImplicitExportLinkagesWithEquivalentSignaturesAgree) {
  ExpectAccepted(R"(
    module m;
      function int sv_f(input int a); return a; endfunction
      export "DPI-C" function sv_f;
    endmodule
    module n;
      function int sv_f(input int b); return b; endfunction
      export "DPI-C" function sv_f;
    endmodule
  )");
}

TEST(DpiGlobalNameElab, ImplicitExportLinkagesWithDifferentResultsDisagree) {
  ExpectReport(R"(
    module m;
      function int sv_f(input int a); return a; endfunction
      export "DPI-C" function sv_f;
    endmodule
    module n;
      function bit sv_f(input int b); return b; endfunction
      export "DPI-C" function sv_f;
    endmodule
  )",
               DifferentSignature("sv_f"), 8);
}

TEST(DpiGlobalNameElab, DuplicateExportLinkageInAnInterfaceIsError) {
  ExpectReport(R"(
    interface ifc;
      function void a(); endfunction
      function void b(); endfunction
      export "DPI-C" link = function a;
      export "DPI-C" link = function b;
    endinterface
    module m;
      ifc i();
    endmodule
  )",
               AlreadyInScope("link"), 6);
}

TEST(DpiGlobalNameElab, DuplicateExportLinkageInAProgramIsError) {
  ExpectReport(R"(
    program p;
      function void a(); endfunction
      function void b(); endfunction
      export "DPI-C" link = function a;
      export "DPI-C" link = function b;
    endprogram
    module m;
      p u();
    endmodule
  )",
               AlreadyInScope("link"), 6);
}

TEST(DpiGlobalNameElab, DuplicateExportLinkageInTheCompilationUnitIsError) {
  ExpectReport(R"(
    function void a(); endfunction
    function void b(); endfunction
    export "DPI-C" link = function a;
    export "DPI-C" link = function b;
    module m;
    endmodule
  )",
               AlreadyInScope("link"), 5);
}

TEST(DpiGlobalNameElab, TwoTasksExportedUnderOneExplicitLinkageIsError) {
  ExpectReport(R"(
    module m;
      task a; endtask
      task b; endtask
      export "DPI-C" link = task a;
      export "DPI-C" link = task b;
    endmodule
  )",
               AlreadyInScope("link"), 6);
}

TEST(DpiGlobalNameElab, ATasksExplicitLinkageEqualToAnothersImplicitIsError) {
  ExpectReport(R"(
    module m;
      task a; endtask
      task b; endtask
      export "DPI-C" a = task b;
      export "DPI-C" task a;
    endmodule
  )",
               AlreadyInScope("a"), 6);
}

TEST(DpiGlobalNameElab, ATaskAndAFunctionExportedUnderOneLinkageIsError) {
  ExpectReport(R"(
    module m;
      task a; endtask
      function void b(); endfunction
      export "DPI-C" link = task a;
      export "DPI-C" link = function b;
    endmodule
  )",
               AlreadyInScope("link"), 6);
}

TEST(DpiGlobalNameElab, TwoTasksExportedUnderOneLinkageInAPackageIsError) {
  ExpectReport(R"(
    package pk;
      task a; endtask
      task b; endtask
      export "DPI-C" link = task a;
      export "DPI-C" link = task b;
    endpackage
    module m;
    endmodule
  )",
               AlreadyInScope("link"), 6);
}

TEST(DpiGlobalNameElab,
     TwoTasksExportedUnderOneLinkageInAGenerateBlockIsError) {
  ExpectReport(R"(
    module m;
      if (1) begin : g
        task a; endtask
        task b; endtask
        export "DPI-C" link = task a;
        export "DPI-C" link = task b;
      end
    endmodule
  )",
               AlreadyInScope("link"), 7);
}

TEST(DpiGlobalNameElab, ImportsOfOneExplicitLinkageDisagreeOnVersionString) {
  ExpectReport(R"(
    module m;
      import "DPI-C" link = function int a(input int x);
    endmodule
    module n;
      import "DPI" link = function int b(input int x);
    endmodule
  )",
               DifferentVersionString("link"), 6);
}

TEST(DpiGlobalNameElab, ImportsOfOneImplicitLinkageDisagreeOnVersionString) {
  ExpectReport(R"(
    module m;
      import "DPI-C" function int sv_f(input int a);
    endmodule
    module n;
      import "DPI" function int sv_f(input int a);
    endmodule
  )",
               DifferentVersionString("sv_f"), 6);
}

TEST(DpiGlobalNameElab, AnImportAndAnImplicitExportDisagreeOnVersionString) {
  ExpectReport(R"(
    module m;
      import "DPI-C" function int sv_f(input int a);
    endmodule
    module n;
      function int sv_f(input int a); return a; endfunction
      export "DPI" function sv_f;
    endmodule
  )",
               DifferentVersionString("sv_f"), 7);
}

TEST(DpiGlobalNameElab, ExportsOfOneExplicitLinkageDisagreeOnVersionString) {
  ExpectReport(R"(
    module m;
      function int a(input int x); return x; endfunction
      export "DPI-C" link = function a;
    endmodule
    module n;
      function int b(input int x); return x; endfunction
      export "DPI" link = function b;
    endmodule
  )",
               DifferentVersionString("link"), 8);
}

TEST(DpiGlobalNameElab, ExportsOfOneImplicitLinkageDisagreeOnVersionString) {
  ExpectReport(R"(
    module m;
      function int sv_f(input int x); return x; endfunction
      export "DPI-C" function sv_f;
    endmodule
    module n;
      function int sv_f(input int x); return x; endfunction
      export "DPI" function sv_f;
    endmodule
  )",
               DifferentVersionString("sv_f"), 8);
}

TEST(DpiGlobalNameElab, ImportsInOneScopeDisagreeOnVersionString) {
  ExpectReport(R"(
    module m;
      import "DPI-C" link = function int a(input int x);
      import "DPI" link = function int b(input int x);
    endmodule
  )",
               DifferentVersionString("link"), 4);
}

TEST(DpiGlobalNameElab, ALinkageNameMayEqualANativeFunctionsName) {
  ExpectAccepted(R"(
    module m;
      function int foo; return 1; endfunction
      import "DPI-C" foo = function void bar();
    endmodule
  )");
}

TEST(DpiGlobalNameElab, AnEscapedKeywordSvNameDefaultsItsStrippedLinkage) {
  ExpectAccepted(R"(
    module m;
      function void \begin ; endfunction
      export "DPI-C" function \begin ;
      import "DPI-C" function void \module ();
    endmodule
  )");
}

TEST(DpiGlobalNameElab, OnlyTheLinkageNameHasToBeACIdentifier) {
  ExpectAccepted(R"(
    module m;
      import "DPI-C" \begin  = function void \init[2] ();
      import "DPI-C" init_1 = function void \init[1] ();
    endmodule
  )");
}

TEST(DpiGlobalNameElab, DISABLED_ADefaultedLinkageThatIsACKeywordIsError) {
  ExpectReport(R"(
    module m;
      function void \if ; endfunction
      export "DPI-C" function \if ;
    endmodule
  )",
               "DPI linkage name 'if'", 4);
}

TEST(DpiGlobalNameElab, DISABLED_AnEscapedLinkageThatIsACKeywordIsError) {
  ExpectReport(R"(
    module m;
      import "DPI-C" \while  = function void w();
    endmodule
  )",
               "DPI linkage name 'while'", 3);
}

}  // namespace
