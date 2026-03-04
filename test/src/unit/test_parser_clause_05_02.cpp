#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserCh501, FreeFormatLayout) {
  EXPECT_TRUE(ParseOk("module t; logic a; endmodule"));
}

TEST(ParserCh501, FreeFormatMultiline) {
  EXPECT_TRUE(
      ParseOk("module\n"
              "  t\n"
              ";\n"
              "  logic\n"
              "    a\n"
              ";\n"
              "endmodule\n"));
}

TEST(ParserCh501, AllTokenTypesPresent) {
  EXPECT_TRUE(
      ParseOk("module t; // one-line comment\n"
              "  /* block comment */\n"
              "  logic [7:0] data = 8'hAB;\n"
              "  initial $display(\"hello\");\n"
              "endmodule\n"));
}

}  // namespace
