#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string WithWeight(const std::string& weight) {
  return "module t;\n"
         "  int x;\n"
         "  real r = 2.5;\n"
         "  initial begin\n"
         "    randcase\n"
         "      " +
         weight +
         " : x = 1;\n"
         "      1 : x = 2;\n"
         "    endcase\n"
         "  end\n"
         "endmodule\n";
}

TEST(RandcaseWeights, DISABLED_ARealLiteralWeightIsRejected) {
  ElabFixture f;
  ElabOk(WithWeight("2.5"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "randcase weight shall be an integral expression",
                            6, "18.16"));
}

TEST(RandcaseWeights, DISABLED_ARealVariableWeightIsRejected) {
  ElabFixture f;
  ElabOk(WithWeight("r"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "randcase weight shall be an integral expression",
                            6, "18.16"));
}

TEST(RandcaseWeights, AnIntegralWeightIsAccepted) {
  EXPECT_TRUE(ElabOk(WithWeight("$rtoi(r)")));
}

}  // namespace
