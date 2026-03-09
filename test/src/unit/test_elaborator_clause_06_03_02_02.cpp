

#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaborator, DriveStrengthOnNetDeclWithoutAssignIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire (strong0, pull1) w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}
