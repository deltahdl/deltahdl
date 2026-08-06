#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §35.5.6.1: "Exported SystemVerilog functions cannot have formal arguments
// specified as open arrays." The open-array relaxation -- an unsized "[]"
// dimension -- is reserved for imports; exporting a SystemVerilog function
// whose formal carries one is an error.
TEST(DpiExportOpenArray, ExportedFunctionWithOpenArrayArgIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_take(input int data[]); endfunction
      export "DPI-C" function sv_take;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

// §35.5.6.1: the open-array allowance applies to imports, not exports. The same
// unsized "[]" formal that disqualifies a function from export is perfectly
// legal on an imported function declaration, so a module that only imports an
// open-array formal elaborates without error -- the asymmetry the subclause
// draws between the two sides of the interface.
TEST(DpiExportOpenArray, ImportedFunctionWithOpenArrayArgIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function void c_take(input int data[]);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

// §35.5.6.1: an export is rejected specifically because the formal's dimension
// is left *unspecified*. A sized unpacked dimension is not an open array, so an
// export carrying one is well-formed -- confirming the rejection keys on the
// open "[]" form rather than on unpacked dimensions in general.
TEST(DpiExportOpenArray, ExportedFunctionWithSizedUnpackedArrayArgIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_take(input int data[4]); endfunction
      export "DPI-C" function sv_take;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
