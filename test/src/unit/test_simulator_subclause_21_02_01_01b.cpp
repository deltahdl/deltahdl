// §21.2.1.1 Format specifications — the unpacked aggregates other than the
// fixed-size array: queues, dynamic and associative arrays, and unpacked
// structs and unions. An integer specifier is barred from each of them, save
// %u and %z on a struct or union; an unpacked array of byte without a
// specifier prints as a character string, and any other unpacked argument
// without one is illegal.
#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
#include <iterator>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The declarations every case below draws on: an int queue, an int dynamic
// array, an int-element associative array and an unpacked struct, each
// holding a value, on lines 2 to 6, with the calls written from line 9 on.
constexpr const char* kAggregates =
    "module t;\n"
    "  typedef struct {int a; int b;} s_t;\n"
    "  s_t s = '{1, 2};\n"
    "  int q[$] = {3, 4};\n"
    "  int d[] = '{5, 6};\n"
    "  int aa[int] = '{7:8};\n"
    "  initial begin\n"
    "    #1;\n";

// §21.2.1.1 (printed page 657): the integer format specifiers shall not be
// used with any unpacked aggregate type, a queue, a dynamic or associative
// array and an unpacked struct among them.
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

// §21.2.1.1 (printed page 657): %u and %z are defined on an unpacked struct,
// so neither is refused there.
TEST(UnpackedAggregateFormat, UnformattedSpecifiersOnAnUnpackedStructAreLegal) {
  SimFixture f;
  RunCapture(std::string(kAggregates) +
                 "    $display(\"%u%z\", s, s);\n"
                 "  end\n"
                 "endmodule\n",
             f);
  EXPECT_FALSE(f.has_errors);
}

// §21.2.1.1 (printed page 656): an expression argument of an unpacked type
// other than an unpacked array of byte, with no format specification of its
// own, is illegal.
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

// §21.2.1.1 (printed page 656): an unpacked array of byte with no format
// specification prints as a character string, and a queue or a dynamic array
// of byte is one as much as a fixed-size array.
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

// Writes `fmt` of the variable `v` that `decl` declares and `init` sets, with
// $fwrite to a scratch file tagged `tag`, and returns the bytes written.
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

// §21.2.1.1 (printed page 657): %u applies to an unpacked struct as though
// performed on each member in declaration order, each member written in
// 32-bit units, so `a` comes out as one word and then `b` as another.
TEST(UnpackedAggregateFormat, UnformattedStructIsWrittenMemberByMember) {
  std::string bytes = UnformattedBytes(
      "struct", "  typedef struct {int a; byte b;} s_t;\n  s_t v;\n",
      "    v.a = 1; v.b = 2;\n", "%u");
  EXPECT_EQ(bytes, std::string("\x01\0\0\0\x02\0\0\0", 8));
}

// §21.2.1.1 (printed page 657): %z applies to an unpacked union as though
// performed on its first member alone, so of a union whose first member is a
// byte only that byte's 32-bit unit -- its aval word, then its bval word -- is
// written, not the whole of the int beside it.
TEST(UnpackedAggregateFormat, UnformattedUnionIsWrittenAsItsFirstMember) {
  std::string bytes = UnformattedBytes(
      "union", "  typedef union {byte b; int a;} u_t;\n  u_t v;\n",
      "    v.a = 32'h11223344;\n", "%z");
  EXPECT_EQ(bytes, std::string("\x44\0\0\0\0\0\0\0", 8));
}

}  // namespace
