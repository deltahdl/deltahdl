#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing, DefaultNettypeTri) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`default_nettype tri\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, DefaultNettypeWand) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`default_nettype wand\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, DefaultNettypeWor) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`default_nettype wor\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, DefaultNettypeTri0) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`default_nettype tri0\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, DefaultNettypeTri1) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`default_nettype tri1\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, DefaultNettypeTriand) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`default_nettype triand\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, DefaultNettypeTrior) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`default_nettype trior\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, DefaultNettypeTrireg) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`default_nettype trireg\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, DefaultNettypeUwire) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`default_nettype uwire\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, DefaultNettypeBeforeAndAfterModule) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`default_nettype none\n"
                              "module t;\n"
                              "endmodule\n"
                              "`default_nettype wire\n"));
}

TEST(CompilerDirectiveParsing, MultipleDefaultNettypeDirectives) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`default_nettype wire\n"
                              "module m1;\n"
                              "endmodule\n"
                              "`default_nettype none\n"
                              "module m2;\n"
                              "endmodule\n"));
}

}  // namespace
