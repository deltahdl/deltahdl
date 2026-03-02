// §22.8: `default_nettype

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection22, DefaultNettypeTri) {
  EXPECT_TRUE(
      ParseOk("`default_nettype tri\n"
              "module t;\n"
              "endmodule\n"));
}

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

}  // namespace
