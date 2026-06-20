#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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

TEST(DataTypeParsing, DefaultNettypeAffectsImplicit) {
  auto r = ParseWithPreprocessor(
      "`default_nettype none\n"
      "module m;\n"
      "  wire w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CompilerDirectiveParsing, DefaultNettypeModuleCount) {
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

TEST(DataTypeParsing, DefaultNettypeWire) {
  auto r = ParseWithPreprocessor(
      "`default_nettype wire\n"
      "module t;\n"
      "  assign out = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->default_nettype, NetType::kWire);
}

TEST(DataTypeParsing, DefaultNettypeNone) {
  auto r = ParseWithPreprocessor(
      "`default_nettype none\n"
      "module t;\n"
      "  wire explicit_w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
}

}  // namespace
