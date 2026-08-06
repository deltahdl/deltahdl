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

// The 9 net-type keywords (tri/wand/wor/tri0/tri1/triand/trior/trireg/uwire)
// are consumed by the preprocessor before the parser runs, so parser behavior
// is identical for every value; DefaultNettypeTri above is the representative
// acceptance case, and per-value NetType mapping is exercised in the
// preprocessor's canonical tests.
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
