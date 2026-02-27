// §10.3.4: Continuous assignment strengths

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// =============================================================================
// §10.3.4 Drive strength — validation
// =============================================================================
TEST(ElabClause1003, Validate_IllegalDriveStrengthHighz0Highz1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, highz1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabClause1003, Validate_IllegalDriveStrengthHighz1Highz0) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz1, highz0) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabClause1003, Validate_LegalDriveStrengthHighz0Strong1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, strong1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
