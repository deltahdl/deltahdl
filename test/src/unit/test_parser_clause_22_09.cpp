#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing, UnconnectedDrivePull1) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`unconnected_drive pull1\n"
                              "module t;\n"
                              "endmodule\n"
                              "`nounconnected_drive\n"));
}

TEST(CompilerDirectiveParsing, UnconnectedDrivePull0) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`unconnected_drive pull0\n"
                              "module t;\n"
                              "endmodule\n"
                              "`nounconnected_drive\n"));
}

TEST(CompilerDirectiveParsing, UnconnectedDrive_NoPairing) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`unconnected_drive pull1\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, NounconnectedDrive_Standalone) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`nounconnected_drive\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, UnconnectedDrive_MultipleModules) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`unconnected_drive pull0\n"
                              "module a;\n"
                              "endmodule\n"
                              "module b;\n"
                              "endmodule\n"
                              "`nounconnected_drive\n"));
}

TEST(CompilerDirectiveParsing, UnconnectedDrive_Supersede) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`unconnected_drive pull0\n"
                              "module a;\n"
                              "endmodule\n"
                              "`unconnected_drive pull1\n"
                              "module b;\n"
                              "endmodule\n"
                              "`nounconnected_drive\n"));
}

TEST(CompilerDirectiveParsing, UnconnectedDrive_InsideModule_Error) {
  EXPECT_FALSE(
      ParseWithPreprocessorOk("module t;\n"
                              "`unconnected_drive pull0\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, NounconnectedDrive_InsideModule_Error) {
  EXPECT_FALSE(
      ParseWithPreprocessorOk("module t;\n"
                              "`nounconnected_drive\n"
                              "endmodule\n"));
}

}  // namespace
