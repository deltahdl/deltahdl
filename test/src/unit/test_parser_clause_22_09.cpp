#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection22, UnconnectedDrivePull1) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`unconnected_drive pull1\n"
                              "module t;\n"
                              "endmodule\n"
                              "`nounconnected_drive\n"));
}

TEST(ParserSection22, UnconnectedDrivePull0) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`unconnected_drive pull0\n"
                              "module t;\n"
                              "endmodule\n"
                              "`nounconnected_drive\n"));
}

TEST(ParserSection22, UnconnectedDrive_NoPairing) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`unconnected_drive pull1\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(ParserSection22, NounconnectedDrive_Standalone) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`nounconnected_drive\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(ParserSection22, UnconnectedDrive_MultipleModules) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`unconnected_drive pull0\n"
                              "module a;\n"
                              "endmodule\n"
                              "module b;\n"
                              "endmodule\n"
                              "`nounconnected_drive\n"));
}

TEST(ParserSection22, UnconnectedDrive_Supersede) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`unconnected_drive pull0\n"
                              "module a;\n"
                              "endmodule\n"
                              "`unconnected_drive pull1\n"
                              "module b;\n"
                              "endmodule\n"
                              "`nounconnected_drive\n"));
}

TEST(ParserSection22, UnconnectedDrive_InsideModule_Error) {
  EXPECT_FALSE(
      ParseWithPreprocessorOk("module t;\n"
                              "`unconnected_drive pull0\n"
                              "endmodule\n"));
}

TEST(ParserSection22, NounconnectedDrive_InsideModule_Error) {
  EXPECT_FALSE(
      ParseWithPreprocessorOk("module t;\n"
                              "`nounconnected_drive\n"
                              "endmodule\n"));
}

}  // namespace
