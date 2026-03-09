#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection22, CelldefineEndcelldefine) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`celldefine\n"
                              "module inv(output y, input a);\n"
                              "  assign y = ~a;\n"
                              "endmodule\n"
                              "`endcelldefine\n"));
}

TEST(ParserSection22, Celldefine_NoPairing) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`celldefine\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(ParserSection22, Endcelldefine_Standalone) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`endcelldefine\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(ParserSection22, Celldefine_MultiplePairs) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`celldefine\n"
                              "module a;\n"
                              "endmodule\n"
                              "`endcelldefine\n"
                              "`celldefine\n"
                              "module b;\n"
                              "endmodule\n"
                              "`endcelldefine\n"));
}

TEST(ParserSection22, Celldefine_InsideModule) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module t;\n"
                              "`celldefine\n"
                              "endmodule\n"
                              "`endcelldefine\n"));
}

}  // namespace
