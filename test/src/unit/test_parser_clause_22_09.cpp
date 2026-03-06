#include "fixture_parser.h"

using namespace delta;

namespace {

// --- §22.9: Module parses between unconnected_drive directives ---

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

// --- §22.9: Directive without `nounconnected_drive (independent directives)
// ---

TEST(ParserSection22, UnconnectedDrive_NoPairing) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`unconnected_drive pull1\n"
                              "module t;\n"
                              "endmodule\n"));
}

// --- §22.9: `nounconnected_drive standalone ---

TEST(ParserSection22, NounconnectedDrive_Standalone) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`nounconnected_drive\n"
                              "module t;\n"
                              "endmodule\n"));
}

// --- §22.9: Multiple modules between directives ---

TEST(ParserSection22, UnconnectedDrive_MultipleModules) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`unconnected_drive pull0\n"
                              "module a;\n"
                              "endmodule\n"
                              "module b;\n"
                              "endmodule\n"
                              "`nounconnected_drive\n"));
}

// --- §22.9: Most recent directive supersedes ---

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

// --- §22.9: Inside design element produces error ---

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
