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

// Only the root segment of the hierarchical name is constrained to a design
// cell; the path below it may descend arbitrarily deep.
TEST(ConfigInstanceClause, DeepInstancePathRootedAtDesignCellAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a.b.c liblist work;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// When the design statement names the cell with a library qualifier, the root
// of an instance path matches the cell name rather than the library name.
TEST(ConfigInstanceClause, InstancePathRootMatchesLibraryQualifiedDesignCell) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design lib1.top;\n"
      "  instance top.a liblist work;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// A library name is not a valid instance-path root; using it instead of the
// cell name is rejected.
TEST(ConfigInstanceClause, InstancePathRootedAtLibraryNameRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design lib1.top;\n"
      "  instance lib1.a liblist work;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
