#include "fixture_elaborator.h"

namespace {

TEST(WhiteSpaceElaboration, SpaceDelimiterElaborates) {
  EXPECT_TRUE(ElabOk("module t; logic a; assign a = 1'b0; endmodule"));
}

TEST(WhiteSpaceElaboration, TabDelimiterElaborates) {
  EXPECT_TRUE(ElabOk("module\tt;\tlogic\ta;\tassign\ta=1'b0;\tendmodule"));
}

TEST(WhiteSpaceElaboration, NewlineDelimiterElaborates) {
  EXPECT_TRUE(
      ElabOk("module\nt\n;\nlogic\na\n;\nassign\na\n=\n1'b0\n;\nendmodule\n"));
}

TEST(WhiteSpaceElaboration, FormfeedDelimiterElaborates) {
  EXPECT_TRUE(ElabOk("module\ft\f;\flogic\fa\f;\fassign\fa=1'b0;\fendmodule"));
}

TEST(WhiteSpaceElaboration, EmptyInputElaboratesNoDesign) {
  ElabFixture f;
  auto* design = ElaborateSrc("", f);
  EXPECT_EQ(design, nullptr);
}

}  // namespace
