#include "fixture_elaborator.h"

namespace {

// §A.9.4: white_space ::= space | tab | newline | formfeed | eof — observed at
// the elaborator stage: each non-EOF alternative must successfully separate
// tokens in a source that elaborates without errors.

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

// §A.9.4 eof alternative (degenerate form): source containing only EOF — no
// preceding chars — must reach elaboration cleanly and yield no design.
TEST(WhiteSpaceElaboration, EmptyInputElaboratesNoDesign) {
  ElabFixture f;
  auto* design = ElaborateSrc("", f);
  EXPECT_EQ(design, nullptr);
}

}  // namespace
