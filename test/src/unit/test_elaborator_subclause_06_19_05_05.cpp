#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(EnumMethods, NumElaboratesOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef enum {RED, GREEN, BLUE} color_e;\n"
             "  color_e c;\n"
             "  int n;\n"
             "  initial n = c.num();\n"
             "endmodule\n"));
}

TEST(EnumMethods, NumResultStillNeedsACastToInitializeAnEnumVar) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_e;\n"
      "  color_e c = c.num();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 3,
                            "6.19.3"));
}

}  // namespace
