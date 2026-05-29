#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §35.4: DPI imports and exports share a global linkage name space distinct
// from the compilation-unit scope. The rules tested here govern how that name
// space is policed across modules and across the import/export boundary.

// §35.4: "Multiple export declarations with the same c_identifier in the
// same scope are forbidden." The linkage identifier defaults to the
// SystemVerilog subroutine name when no c_identifier is given, so two
// export declarations of the same function in one scope collide under that
// defaulted name.
TEST(DpiGlobalNameElab, DuplicateDefaultExportLinkageInSameScopeIsError) {
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

// §35.4: every declaration sharing one linkage identifier must agree on the
// DPI version string ("DPI-C" vs the deprecated "DPI"). A mix across an
// import and an export is rejected.
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

}  // namespace
