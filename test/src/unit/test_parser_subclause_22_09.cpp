#include "fixture_parser.h"
#include "helpers_reported_error.h"

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
  auto result = ParseWithPreprocessor(
      "module t;\n"
      "`unconnected_drive pull0\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(result.diags,
                            "`unconnected_drive illegal inside a design "
                            "element",
                            2, "22.9"));
}

TEST(CompilerDirectiveParsing, NounconnectedDrive_InsideModule_Error) {
  auto result = ParseWithPreprocessor(
      "module t;\n"
      "`nounconnected_drive\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(result.diags,
                            "`nounconnected_drive illegal inside a design "
                            "element",
                            2, "22.9"));
}

}  // namespace
