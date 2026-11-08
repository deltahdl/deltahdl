#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DpiExportOpenArray, ExportedFunctionWithOpenArrayArgIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_take(input int data[]); endfunction
      export "DPI-C" function sv_take;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "SystemVerilog function 'sv_take' has a dynamic array", 4, "35.5.6"));
}

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
