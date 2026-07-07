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
