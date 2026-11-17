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

TEST(UnpackedAggregateFormat,
     APackedUnionTakesEveryIntegerSpecifierAsItsVector) {
  for (const char* spec : {"%h", "%x", "%d", "%o", "%b", "%c", "%u", "%z"}) {
    SimFixture f;
    std::string out = RunCapture(
        std::string("module t;\n  union packed { logic [7:0] a; logic [7:0] b; "
                    "} v;\n  logic [7:0] w;\n  initial begin\n    v.a = "
                    "8'hA5;\n    w = 8'hA5;\n    $write(\"") +
            spec + "|\", v);\n    $write(\"" + spec +
            "\", w);\n  end\nendmodule\n",
        f);
    size_t bar = out.find('|');
    ASSERT_NE(bar, std::string::npos) << spec;
    EXPECT_EQ(out.substr(0, bar), out.substr(bar + 1)) << spec;
    EXPECT_EQ(f.diag.ErrorCount(), 0u) << spec;
  }
}

TEST(UnpackedAggregateFormat,
     ATwoDimensionalPackedArrayTakesEveryIntegerSpecifierAsItsVector) {
  for (const char* spec : {"%h", "%x", "%d", "%o", "%b", "%c", "%u", "%z"}) {
    SimFixture f;
    std::string out = RunCapture(
        std::string(
            "module t;\n  logic [1:0][3:0] v;\n  logic [7:0] w;\n  initial "
            "begin\n    v = 8'h3C;\n    w = 8'h3C;\n    $write(\"") +
            spec + "|\", v);\n    $write(\"" + spec +
            "\", w);\n  end\nendmodule\n",
        f);
    size_t bar = out.find('|');
    ASSERT_NE(bar, std::string::npos) << spec;
    EXPECT_EQ(out.substr(0, bar), out.substr(bar + 1)) << spec;
    EXPECT_EQ(f.diag.ErrorCount(), 0u) << spec;
  }
}

TEST(UnpackedAggregateFormat,
     AThreeDimensionalPackedArrayTakesEveryIntegerSpecifierAsItsVector) {
  for (const char* spec : {"%h", "%x", "%d", "%o", "%b", "%c", "%u", "%z"}) {
    SimFixture f;
    std::string out = RunCapture(
        std::string(
            "module t;\n  bit [1:0][1:0][3:0] v;\n  bit [15:0] w;\n  initial "
            "begin\n    v = 16'h1234;\n    w = 16'h1234;\n    $write(\"") +
            spec + "|\", v);\n    $write(\"" + spec +
            "\", w);\n  end\nendmodule\n",
        f);
    size_t bar = out.find('|');
    ASSERT_NE(bar, std::string::npos) << spec;
    EXPECT_EQ(out.substr(0, bar), out.substr(bar + 1)) << spec;
    EXPECT_EQ(f.diag.ErrorCount(), 0u) << spec;
  }
}

TEST(UnpackedAggregateFormat,
     ATypedefOfAPackedStructTypedefTakesEveryIntegerSpecifier) {
  for (const char* spec : {"%h", "%x", "%d", "%o", "%b", "%c", "%u", "%z"}) {
    SimFixture f;
    std::string out = RunCapture(
        std::string(
            "module t;\n  typedef struct packed { logic [3:0] h; logic [3:0] "
            "l; } p_t;\n  typedef p_t q_t;\n  q_t v;\n  logic [7:0] w;\n  "
            "initial begin\n    v = 8'h5A;\n    w = 8'h5A;\n    $write(\"") +
            spec + "|\", v);\n    $write(\"" + spec +
            "\", w);\n  end\nendmodule\n",
        f);
    size_t bar = out.find('|');
    ASSERT_NE(bar, std::string::npos) << spec;
    EXPECT_EQ(out.substr(0, bar), out.substr(bar + 1)) << spec;
    EXPECT_EQ(f.diag.ErrorCount(), 0u) << spec;
  }
}

TEST(UnpackedAggregateFormat, AnEnumTakesEveryIntegerSpecifierAsItsBaseValue) {
  for (const char* spec : {"%h", "%x", "%d", "%o", "%b", "%c", "%u", "%z"}) {
    SimFixture f;
    std::string out =
        RunCapture(std::string("module t;\n  enum logic [7:0] {A = 8'h41, B = "
                               "8'h42} v;\n  logic [7:0] w;\n  initial begin\n "
                               "   v = B;\n    w = 8'h42;\n    $write(\"") +
                       spec + "|\", v);\n    $write(\"" + spec +
                       "\", w);\n  end\nendmodule\n",
                   f);
    size_t bar = out.find('|');
    ASSERT_NE(bar, std::string::npos) << spec;
    EXPECT_EQ(out.substr(0, bar), out.substr(bar + 1)) << spec;
    EXPECT_EQ(f.diag.ErrorCount(), 0u) << spec;
  }
}

TEST(UnpackedAggregateFormat,
     APackedStructTakesEveryIntegerSpecifierAsItsVector) {
  for (const char* spec : {"%h", "%x", "%d", "%o", "%b", "%c", "%u", "%z"}) {
    SimFixture f;
    std::string out = RunCapture(
        std::string("module t;\n  struct packed { logic [3:0] h; logic [3:0] "
                    "l; } v;\n  logic [7:0] w;\n  initial begin\n    v = "
                    "8'hC3;\n    w = 8'hC3;\n    $write(\"") +
            spec + "|\", v);\n    $write(\"" + spec +
            "\", w);\n  end\nendmodule\n",
        f);
    size_t bar = out.find('|');
    ASSERT_NE(bar, std::string::npos) << spec;
    EXPECT_EQ(out.substr(0, bar), out.substr(bar + 1)) << spec;
    EXPECT_EQ(f.diag.ErrorCount(), 0u) << spec;
  }
}

TEST(UnpackedAggregateFormat, UnformattedWiderThan32BitsWritesTheLowUnitFirst) {
  std::string bytes = UnformattedBytes(
      "u64", "  logic [63:0] v;\n", "    v = 64'h11223344_55667788;\n", "%u");
  EXPECT_EQ(bytes, std::string("\x88\x77\x66\x55\x44\x33\x22\x11", 8));
}

TEST(UnpackedAggregateFormat,
     FourValueWiderThan32BitsWritesEachUnitsPairLowFirst) {
  std::string bytes = UnformattedBytes(
      "z64", "  logic [63:0] v;\n", "    v = 64'h1122334x_5566778z;\n", "%z");
  EXPECT_EQ(bytes, std::string("\x80\x77\x66\x55\x0f\0\0\0"
                               "\x4f\x33\x22\x11\x0f\0\0\0",
                               16));
}

TEST(UnpackedAggregateFormat, TwoValueUnionIsWrittenAsItsFirstMember) {
  std::string bytes = UnformattedBytes(
      "u_union", "  typedef union {byte b; int a;} u_t;\n  u_t v;\n",
      "    v.a = 32'h11223344;\n", "%u");
  EXPECT_EQ(bytes, std::string("\x44\0\0\0", 4));
}

TEST(UnpackedAggregateFormat, FourValueStructIsWrittenMemberByMember) {
  std::string bytes = UnformattedBytes(
      "z_struct", "  typedef struct {int a; byte b;} s_t;\n  s_t v;\n",
      "    v.a = 1; v.b = 2;\n", "%z");
  EXPECT_EQ(bytes, std::string("\x01\0\0\0\0\0\0\0\x02\0\0\0\0\0\0\0", 16));
}

TEST(UnpackedAggregateFormat, PercentOOnAnUnpackedStructIsReported) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  typedef struct {int a; int b;} s_t;\n"
      "  s_t s = '{1, 2};\n"
      "  initial begin\n"
      "    #1;\n"
      "    $display(\"%o\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an integer format specifier cannot be applied", 6,
                            "21.2.1.1"));
}

TEST(UnpackedAggregateFormat, PercentXOnAnUnpackedStructIsReported) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  typedef struct {int a; int b;} s_t;\n"
      "  s_t s = '{1, 2};\n"
      "  initial begin\n"
      "    #1;\n"
      "    $display(\"%x\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an integer format specifier cannot be applied", 6,
                            "21.2.1.1"));
}

TEST(UnpackedAggregateFormat, PercentCOnAnUnpackedStructIsReported) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  typedef struct {int a; int b;} s_t;\n"
      "  s_t s = '{1, 2};\n"
      "  initial begin\n"
      "    #1;\n"
      "    $display(\"%c\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an integer format specifier cannot be applied", 6,
                            "21.2.1.1"));
}

TEST(UnpackedAggregateFormat, PercentDOnAnUnpackedUnionIsReported) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  typedef union {int a; int b;} u_t;\n"
      "  u_t u;\n"
      "  initial begin\n"
      "    #1;\n"
      "    $display(\"%d\", u);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an integer format specifier cannot be applied", 6,
                            "21.2.1.1"));
}

TEST(UnpackedAggregateFormat, PercentHOnAnUnpackedUnionIsReported) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  typedef union {int a; int b;} u_t;\n"
      "  u_t u;\n"
      "  initial begin\n"
      "    #1;\n"
      "    $display(\"%h\", u);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an integer format specifier cannot be applied", 6,
                            "21.2.1.1"));
}

TEST(UnpackedAggregateFormat, PercentUOnAnUnpackedUnionIsAccepted) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  typedef union {int a; int b;} u_t;\n"
      "  u_t u;\n"
      "  initial begin\n"
      "    #1;\n"
      "    $write(\"%u\", u);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(UnpackedAggregateFormat, PercentZOnAnUnpackedUnionIsAccepted) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  typedef union {int a; int b;} u_t;\n"
      "  u_t u;\n"
      "  initial begin\n"
      "    #1;\n"
      "    $write(\"%z\", u);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(UnpackedAggregateFormat, PercentUOnAFixedArrayIsReported) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  int v[2] = '{1, 2};\n"
      "  initial begin\n"
      "    #1;\n"
      "    $write(\"%u\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an integer format specifier cannot be applied", 5,
                            "21.2.1.1"));
}

TEST(UnpackedAggregateFormat, PercentZOnAQueueIsReported) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  int v[$] = {1, 2};\n"
      "  initial begin\n"
      "    #1;\n"
      "    $write(\"%z\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an integer format specifier cannot be applied", 5,
                            "21.2.1.1"));
}

TEST(UnpackedAggregateFormat, PercentUOnADynamicArrayIsReported) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  int v[] = '{1, 2};\n"
      "  initial begin\n"
      "    #1;\n"
      "    $write(\"%u\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an integer format specifier cannot be applied", 5,
                            "21.2.1.1"));
}

TEST(UnpackedAggregateFormat, PercentZOnADynamicArrayIsReported) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  int v[] = '{1, 2};\n"
      "  initial begin\n"
      "    #1;\n"
      "    $write(\"%z\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an integer format specifier cannot be applied", 5,
                            "21.2.1.1"));
}

TEST(UnpackedAggregateFormat, PercentUOnAnAssociativeArrayIsReported) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  int v[int] = '{1:2};\n"
      "  initial begin\n"
      "    #1;\n"
      "    $write(\"%u\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an integer format specifier cannot be applied", 5,
                            "21.2.1.1"));
}

TEST(UnpackedAggregateFormat, PercentZOnAnAssociativeArrayIsReported) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  int v[int] = '{1:2};\n"
      "  initial begin\n"
      "    #1;\n"
      "    $write(\"%z\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an integer format specifier cannot be applied", 5,
                            "21.2.1.1"));
}

TEST(UnpackedAggregateFormat,
     DISABLED_ABareAssociativeArrayOfBytePrintsInIndexOrder) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  byte v[int];\n"
                       "  initial begin\n"
                       "    v[2] = \"b\";\n"
                       "    v[1] = \"a\";\n"
                       "    $display(v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "ab\n");
}

TEST(UnpackedAggregateFormat, ABareUnpackedUnionIsReported) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  typedef union {int a; int b;} u_t;\n"
      "  u_t u;\n"
      "  initial begin\n"
      "    #1;\n"
      "    $display(u);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unformatted unpacked argument", 6, "21.2.1.1"));
}

TEST(UnpackedAggregateFormat,
     DISABLED_AnUnformattedReadFillingAStructCountsOneItem) {
  SimFixture f;
  std::string path =
      "/tmp/"
      "deltahdl_t21020101b_AnUnformattedReadFillingAStructCountsOneItem.bin";
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {int a; int b;} s_t;\n"
                       "  s_t r;\n"
                       "  integer fd, n;\n"
                       "  initial begin\n"
                       "    fd = $fopen(\"" +
                           path +
                           "\", \"wb\");\n"
                           "    $fwrite(fd, \"%u%u\", 32'd1, 32'd2);\n"
                           "    $fclose(fd);\n"
                           "    fd = $fopen(\"" +
                           path +
                           "\", \"rb\");\n"
                           "    n = $fscanf(fd, \"%u\", r);\n"
                           "    $display(\"%0d\", n);\n"
                           "  end\n"
                           "endmodule\n",
                       f),
            "1\n");
  std::remove(path.c_str());
}

TEST(UnpackedAggregateFormat, AnUnformattedReadShortOfAStructCountsNoItem) {
  SimFixture f;
  std::string path =
      "/tmp/"
      "deltahdl_t21020101b_AnUnformattedReadShortOfAStructCountsNoItem.bin";
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {int a; int b;} s_t;\n"
                       "  s_t r;\n"
                       "  integer fd, n;\n"
                       "  initial begin\n"
                       "    fd = $fopen(\"" +
                           path +
                           "\", \"wb\");\n"
                           "    $fwrite(fd, \"%u\", 32'd1);\n"
                           "    $fclose(fd);\n"
                           "    fd = $fopen(\"" +
                           path +
                           "\", \"rb\");\n"
                           "    n = $fscanf(fd, \"%u\", r);\n"
                           "    $display(\"%0d\", n);\n"
                           "  end\n"
                           "endmodule\n",
                       f),
            "0\n");
  std::remove(path.c_str());
}

}  // namespace
