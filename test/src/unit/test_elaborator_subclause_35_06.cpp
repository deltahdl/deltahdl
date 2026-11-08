#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DpiImportCallBinding, NamedBindingOnAnImportWithUnnamedFormalsIsReported) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int sv_f(input int, input int);
      int r;
      initial r = sv_f(.a(1), .b(2));
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "no parameter 'a' in 'sv_f'",
                            5, "13.5.4"));
}

TEST(DpiImportCallBinding, PositionalBindingOnAnImportWithUnnamedFormalsIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int sv_f(input int, input int);
      int r;
      initial r = sv_f(1, 2);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
