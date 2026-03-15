// Non-LRM tests

#include "fixture_elaborator.h"

namespace {

TEST(DesignBuildingBlockElaboration, PortCommunicationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module inv(input logic a, output logic y);\n"
      "  assign y = ~a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  inv u0(.a(x), .y(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DesignHierarchy, UnknownTopIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; endmodule\n", f, "nonexistent");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
