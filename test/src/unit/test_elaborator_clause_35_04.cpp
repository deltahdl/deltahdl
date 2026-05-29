#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §35.4: DPI imports and exports share a global linkage name space distinct
// from the compilation-unit scope. The rules tested here govern how that name
// space is policed across modules and across the import/export boundary.

// §35.4: "Multiple export declarations with the same c_identifier in the
// same scope are forbidden."
TEST(DpiGlobalNameElab, DuplicateExplicitExportLinkageInSameScopeIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      export "DPI-C" link = function sv_a;
      export "DPI-C" link = function sv_b;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(DpiGlobalNameElab, DuplicateDefaultExportLinkageInSameScopeIsError) {
  // §35.4: the linkage identifier defaults to the SystemVerilog subroutine
  // name when no c_identifier is given. Two export declarations that default
  // to the same name therefore collide in the same scope.
  ElabFixture f;
  Elaborate(R"(
    module m;
      export "DPI-C" function sv_same;
      export "DPI-C" function sv_same;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

// §35.4: "Multiple export declarations are allowed with the same
// c_identifier, explicit or implicit, as long as they are in different
// scopes ..." — exporting the same name from two distinct modules is OK.
TEST(DpiGlobalNameElab, SameExportLinkageAcrossDifferentScopesIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      export "DPI-C" link = function sv_a;
    endmodule
    module n;
      export "DPI-C" link = function sv_b;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

// §35.4: when an import and an export share the same c_identifier they must
// agree on the DPI version string ("DPI-C" vs the deprecated "DPI"). A mix is
// rejected.
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
  EXPECT_TRUE(f.has_errors);
}

// §35.4: two exports of the same c_identifier in different scopes must use
// the same DPI version string.
TEST(DpiGlobalNameElab, TwoExportsSameLinkageDifferentVersionStringIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      export "DPI-C" link = function sv_a;
    endmodule
    module n;
      export "DPI" link = function sv_b;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

// §35.4: matching version strings on import + export sharing a c_identifier
// is the well-formed case. The elaborator must accept it.
TEST(DpiGlobalNameElab, ImportExportSameLinkageSameVersionStringIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function int f(input int x);
    endmodule
    module n;
      export "DPI-C" link = function sv_g;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

// §35.4: when the c_identifier defaults to the SystemVerilog name, the same
// version-string consistency rule still applies. Two decls both defaulting
// their linkage name to "shared" but disagreeing on the version string must
// be rejected.
TEST(DpiGlobalNameElab,
     DefaultedLinkageNameSharedAcrossDeclsRequiresMatchingVersion) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      export "DPI-C" function shared;
    endmodule
    module n;
      export "DPI" function shared;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

// §35.4: two exports of the same SystemVerilog function in distinct scopes
// with the same (default) version string is permitted.
TEST(DpiGlobalNameElab,
     DefaultedLinkageNameSharedAcrossDeclsMatchingVersionIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      export "DPI-C" function shared;
    endmodule
    module n;
      export "DPI-C" function shared;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
