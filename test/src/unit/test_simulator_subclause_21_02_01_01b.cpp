#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
#include <ios>
#include <iterator>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kAggregates =
    "module t;\n"
    "  typedef struct {int a; int b;} s_t;\n"
    "  s_t s = '{1, 2};\n"
    "  int q[$] = {3, 4};\n"
    "  int d[] = '{5, 6};\n"
    "  int aa[int] = '{7:8};\n"
    "  initial begin\n"
    "    #1;\n";

TEST(UnpackedAggregateFormat,
     IntegerSpecifierOnEachUnpackedAggregateIsIllegal) {
  SimFixture f;
  RunCapture(std::string(kAggregates) +
                 "    $display(\"%d\", q);\n"
                 "    $display(\"%h\", d);\n"
                 "    $display(\"%b\", aa);\n"
                 "    $display(\"%d\", s);\n"
                 "  end\n"
                 "endmodule\n",
             f);
  for (int line : {9, 10, 11, 12}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "an integer format specifier cannot be applied",
                              line, "21.2.1.1"))
        << line;
  }
}

TEST(UnpackedAggregateFormat, UnformattedSpecifiersOnAnUnpackedStructAreLegal) {
  SimFixture f;
  RunCapture(std::string(kAggregates) +
                 "    $display(\"%u%z\", s, s);\n"
                 "  end\n"
                 "endmodule\n",
             f);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedAggregateFormat, BareNonByteUnpackedArgumentIsIllegal) {
  SimFixture f;
  RunCapture(std::string(kAggregates) +
                 "    $display(q);\n"
                 "    $display(d);\n"
                 "    $display(aa);\n"
                 "    $display(s);\n"
                 "  end\n"
                 "endmodule\n",
             f);
  for (int line : {9, 10, 11, 12}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "unformatted unpacked argument", line,
                              "21.2.1.1"))
        << line;
  }
}

TEST(UnpackedAggregateFormat, BareByteQueueAndDynamicArrayPrintAsText) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  byte q[$] = {8'h68, 8'h69};\n"
      "  byte d[] = '{8'h6f, 8'h6b};\n"
      "  initial begin\n"
      "    #1;\n"
      "    $display(q);\n"
      "    $display(d);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "hi\nok\n");
}

std::string UnformattedBytes(const std::string& tag, const std::string& decl,
                             const std::string& init, const std::string& fmt) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t21020101b_" + tag + ".bin";
  RunCapture("module t;\n" + decl +
                 "  integer fd;\n"
                 "  initial begin\n" +
                 init + "    fd = $fopen(\"" + path +
                 "\", \"wb\");\n"
                 "    $fwrite(fd, \"" +
                 fmt +
                 "\", v);\n"
                 "    $fclose(fd);\n"
                 "  end\n"
                 "endmodule\n",
             f);
  std::ifstream ifs(path, std::ios::binary);
  std::string bytes((std::istreambuf_iterator<char>(ifs)),
                    std::istreambuf_iterator<char>());
  std::remove(path.c_str());
  return bytes;
}

TEST(UnpackedAggregateFormat, UnformattedStructIsWrittenMemberByMember) {
  std::string bytes = UnformattedBytes(
      "struct", "  typedef struct {int a; byte b;} s_t;\n  s_t v;\n",
      "    v.a = 1; v.b = 2;\n", "%u");
  EXPECT_EQ(bytes, std::string("\x01\0\0\0\x02\0\0\0", 8));
}

TEST(UnpackedAggregateFormat, UnformattedUnionIsWrittenAsItsFirstMember) {
  std::string bytes = UnformattedBytes(
      "union", "  typedef union {byte b; int a;} u_t;\n  u_t v;\n",
      "    v.a = 32'h11223344;\n", "%z");
  EXPECT_EQ(bytes, std::string("\x44\0\0\0\0\0\0\0", 8));
}

}  // namespace
