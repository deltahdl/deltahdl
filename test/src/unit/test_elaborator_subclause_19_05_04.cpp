#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §19.5.4: a wildcard bin is not allowed on a coverpoint of a real type,
// though an integral coverpoint may declare one.
TEST(WildcardBins, WildcardBinOfRealCoverpointIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  bit [3:0] v;\n"
      "  covergroup cg;\n"
      "    coverpoint r {\n"
      "      wildcard bins w = {[1.0:2.0]};\n"
      "      bins b = {[1.0:2.0]};\n"
      "    }\n"
      "    coverpoint v { wildcard bins x = {4'b11??}; }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a bin of a real coverpoint cannot be 'wildcard'",
                            6, "19.5.4"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
