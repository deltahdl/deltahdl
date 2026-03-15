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

TEST(WhiteSpaceElaboration, VerticalTabDelimiterElaborates) {
  EXPECT_TRUE(ElabOk("module\vt\v;\vlogic\va\v;\vassign\va=1'b0;\vendmodule"));
}

TEST(WhiteSpaceElaboration, CrlfDelimiterElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\r\n  logic a;\r\n  assign a = 1'b0;\r\nendmodule\r\n"));
}

TEST(WhiteSpaceElaboration, MixedWhitespaceElaborates) {
  EXPECT_TRUE(
      ElabOk("module \t\n\f\v t \t\n ; \f\v logic \t a ; endmodule"));
}

TEST(WhiteSpaceElaboration, WhitespaceOnlyInputElaboratesEmpty) {
  ElabFixture f;
  auto* design = ElaborateSrc("   \t\n\f\v   ", f);
  EXPECT_EQ(design, nullptr);
}

TEST(WhiteSpaceElaboration, WhitespaceVariationsElaborateIdentically) {
  ElabFixture f1;
  auto* with_spaces =
      ElaborateSrc("module t; logic a; assign a = 1'b0; endmodule", f1);
  ElabFixture f2;
  auto* with_tabs =
      ElaborateSrc("module\tt;\tlogic\ta;\tassign\ta=1'b0;\tendmodule", f2);
  ASSERT_NE(with_spaces, nullptr);
  ASSERT_NE(with_tabs, nullptr);
  EXPECT_FALSE(f1.has_errors);
  EXPECT_FALSE(f2.has_errors);
}

TEST(WhiteSpaceElaboration, BlanksInStringLiteralElaborate) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial $display(\"  hello   world  \");\n"
             "endmodule\n"));
}

TEST(WhiteSpaceElaboration, TabsInStringLiteralElaborate) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial $display(\"\thello\tworld\t\");\n"
             "endmodule\n"));
}

}  // namespace
