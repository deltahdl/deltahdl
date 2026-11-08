#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ScopeRandomizeName, ABareRandomizeReadResolvesAsTheScopeCall) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int ok;\n"
      "  function int f; return randomize; endfunction\n"
      "  initial begin\n"
      "    ok = randomize;\n"
      "    ok = randomize + nosuch;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'nosuch'", 6,
                            "23.9"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
