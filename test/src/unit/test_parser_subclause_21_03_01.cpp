#include "fixture_parser.h"

using namespace delta;

namespace {

// Syntax 21-4: file_open_function permits both the multi-channel-descriptor
// form (no type argument) and the file-descriptor form (with type argument);
// file_close_task accepts either kind of descriptor.

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
