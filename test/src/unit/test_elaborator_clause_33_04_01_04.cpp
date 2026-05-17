#include "fixture_elaborator.h"

namespace {

TEST(ConfigCellClause, LibQualifiedCellWithLiblistRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  cell rtlLib.adder liblist gateLib;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(ConfigCellClause, UnqualifiedCellWithLiblistAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  cell adder liblist gateLib;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigCellClause, LibQualifiedCellWithUseClauseAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  cell rtlLib.adder use gateLib.alt;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

}
