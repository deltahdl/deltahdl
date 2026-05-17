#include "fixture_elaborator.h"

namespace {

TEST(ConfigInstanceClause, InstancePathStartingOutsideDesignIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance other.a liblist work;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(ConfigInstanceClause, InstancePathStartingAtDesignCellAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a liblist work;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigInstanceClause, BareTopLevelInstancePathAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top liblist work;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigInstanceClause, InstancePathPicksAmongMultipleDesignCells) {
  ElabFixture f;
  ElaborateSrc(
      "module top1; endmodule\n"
      "module top2; endmodule\n"
      "config c;\n"
      "  design top1 top2;\n"
      "  instance top2.x liblist work;\n"
      "endconfig\n",
      f, "top1");
  EXPECT_FALSE(f.has_errors);
}

}
