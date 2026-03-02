// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection22, DefaultNettypeWand) {
  EXPECT_TRUE(
      ParseOk("`default_nettype wand\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeWor) {
  EXPECT_TRUE(
      ParseOk("`default_nettype wor\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeTri0) {
  EXPECT_TRUE(
      ParseOk("`default_nettype tri0\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeTri1) {
  EXPECT_TRUE(
      ParseOk("`default_nettype tri1\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeTriand) {
  EXPECT_TRUE(
      ParseOk("`default_nettype triand\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeTrior) {
  EXPECT_TRUE(
      ParseOk("`default_nettype trior\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeTrireg) {
  EXPECT_TRUE(
      ParseOk("`default_nettype trireg\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeUwire) {
  EXPECT_TRUE(
      ParseOk("`default_nettype uwire\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeBeforeAndAfterModule) {
  EXPECT_TRUE(
      ParseOk("`default_nettype none\n"
              "module t;\n"
              "endmodule\n"
              "`default_nettype wire\n"));
}

TEST(ParserSection22, MultipleDefaultNettypeDirectives) {
  EXPECT_TRUE(
      ParseOk("`default_nettype wire\n"
              "module m1;\n"
              "endmodule\n"
              "`default_nettype none\n"
              "module m2;\n"
              "endmodule\n"));
}

// ============================================================================
// AST-level checks for `default_nettype
// ============================================================================
TEST(ParserSection22, DefaultNettypeModuleCount) {
  auto r = ParseWithPreprocessor(
      "`default_nettype wire\n"
      "module m1;\n"
      "endmodule\n"
      "`default_nettype none\n"
      "module m2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->name, "m1");
  EXPECT_EQ(r.cu->modules[1]->name, "m2");
}

TEST(ParserSection22, UnconnectedDrivePull1) {
  EXPECT_TRUE(
      ParseOk("`unconnected_drive pull1\n"
              "module t;\n"
              "endmodule\n"
              "`nounconnected_drive\n"));
}

TEST(ParserSection22, UnconnectedDrivePull0) {
  EXPECT_TRUE(
      ParseOk("`unconnected_drive pull0\n"
              "module t;\n"
              "endmodule\n"
              "`nounconnected_drive\n"));
}

TEST(ParserSection22, CelldefineEndcelldefine) {
  EXPECT_TRUE(
      ParseOk("`celldefine\n"
              "module inv(output y, input a);\n"
              "  assign y = ~a;\n"
              "endmodule\n"
              "`endcelldefine\n"));
}

// ============================================================================
// LRM section 22.13 -- `__FILE__ and `__LINE__
// ============================================================================
TEST(ParserSection22, FileDirectiveInDisplay) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"File: %s\", `__FILE__);\n"
              "endmodule\n"));
}

TEST(ParserSection22, LineDirectiveInDisplay) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"Line: %0d\", `__LINE__);\n"
              "endmodule\n"));
}

}  // namespace
