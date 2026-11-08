#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, FopenFcloseCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  initial begin\n"
              "    fd = $fopen(\"output.log\", \"w\");\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, FopenMcdFormWithoutType) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer mcd;\n"
              "  initial begin\n"
              "    mcd = $fopen(\"channel.log\");\n"
              "    $fclose(mcd);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, FopenAcceptsAllDocumentedModeStrings) {
  for (const char* type : {"r", "rb", "w", "wb", "a", "ab", "r+", "r+b", "rb+",
                           "w+", "w+b", "wb+", "a+", "a+b", "ab+"}) {
    std::string src = std::string(
                          "module t;\n"
                          "  integer fd;\n"
                          "  initial begin\n"
                          "    fd = $fopen(\"f.dat\", \"") +
                      type +
                      "\");\n"
                      "    $fclose(fd);\n"
                      "  end\n"
                      "endmodule\n";
    EXPECT_TRUE(ParseOk(src)) << "type=" << type;
  }
}

}  // namespace
