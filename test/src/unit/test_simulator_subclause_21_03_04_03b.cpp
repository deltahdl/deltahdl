#include <gtest/gtest.h>

#include <cstdio>
#include <string>

#include "fixture_simulator.h"
#include "helpers_placeholder_paths.h"
#include "helpers_reported_error.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

TEST(ScanfDestinations, ClassPropertiesAndElementsTakeTheFields) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t21030403_props.txt";
  SeedFile(path, "12 world\n");
  std::string out = RunCapture(
      "module t;\n"
      "  class R;\n"
      "    string s; int n; string w; int k;\n"
      "    function void scan; void'($sscanf(\"41\", \"%d\", k)); endfunction\n"
      "  endclass\n"
      "  R r = new;\n"
      "  integer fd, c;\n"
      "  int arr[3];\n"
      "  initial begin\n"
      "    c = $sscanf(\"word\", \"%s\", r.s);\n"
      "    $display(\"%0d %s\", c, r.s);\n"
      "    fd = $fopen(\"" +
          path +
          "\", \"r\");\n"
          "    c = $fscanf(fd, \"%d %s\", r.n, r.w);\n"
          "    $display(\"%0d %0d %s\", c, r.n, r.w);\n"
          "    $fclose(fd);\n"
          "    r.scan();\n"
          "    $display(\"%0d\", r.k);\n"
          "    c = $sscanf(\"5\", \"%d\", arr[1]);\n"
          "    $display(\"%0d %0d\", c, arr[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "1 word\n2 12 world\n41\n1 5\n");
  std::remove(path.c_str());
}

TEST(ScanfDestinations, IntegerCodesIntoUnpackedAggregatesAreRefused) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {int a; int b;} s_t;\n"
      "  typedef union {int a; byte b;} u_t;\n"
      "  s_t s; u_t u; int q[$]; int aa[int];\n"
      "  integer c;\n"
      "  initial begin\n"
      "    c = $sscanf(\"5\", \"%d\", s);\n"
      "    c = $sscanf(\"5\", \"%u\", u);\n"
      "    c = $sscanf(\"5\", \"%d\", q);\n"
      "    c = $sscanf(\"5\", \"%h\", aa);\n"
      "    $display(\"%0d %0d %0d\", s.a, q.size(), aa.num());\n"
      "  end\n"
      "endmodule\n",
      f);
  for (int line : {7, 8, 9, 10}) {
    EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                                "may not read into unpacked aggregate", line,
                                "21.3.4.3"))
        << line;
  }
  EXPECT_EQ(out, "0 0 0\n");
}

struct ByteScan {
  std::string decl;
  std::string scan;
  std::string show;
};

std::string ScanBytes(const std::string& tag, const std::string& bytes,
                      const ByteScan& c, SimFixture& f) {
  SeedFile(PlaceholderPath("t2134403", tag, 0), bytes);
  std::string out =
      RunWithPlaceholderPaths("t2134403", tag,
                              "module t;\n" + c.decl +
                                  "\n"
                                  "  integer fd, n;\n"
                                  "  initial begin\n"
                                  "    fd = $fopen(\"<P0>\", \"rb\");\n"
                                  "    n = " +
                                  c.scan +
                                  ";\n"
                                  "    $display(\"%0d \", n, " +
                                  c.show +
                                  ");\n"
                                  "    $fclose(fd);\n"
                                  "  end\n"
                                  "endmodule\n",
                              f);
  RemovePlaceholderPaths("t2134403", tag);
  return out;
}

TEST(ScanfDestinations, UnformattedTwoValueReadsInNativeOrder) {
  SimFixture f;
  EXPECT_EQ(ScanBytes("u32", std::string("\x11\x22\x33\x44", 4),
                      {"  reg [31:0] v;", "$fscanf(fd, \"%u\", v)",
                       "v == 32'h44332211"},
                      f),
            "1 1\n");
}

TEST(ScanfDestinations, UnformattedFourValueReadsAvalThenBvalInNativeOrder) {
  SimFixture f;
  EXPECT_EQ(ScanBytes("z32", std::string("\x11\x22\x33\x44\x03\x00\x00\x00", 8),
                      {"  logic [31:0] v;", "$fscanf(fd, \"%z\", v)",
                       "v === 32'b0100_0100_0011_0011_0010_0010_0001_00zx"},
                      f),
            "1 1\n");
}

TEST(ScanfDestinations, UnformattedTwoValueFillsAWideTargetLowChunkFirst) {
  SimFixture f;
  EXPECT_EQ(ScanBytes("u72",
                      std::string("\x11\x22\x33\x44\x55\x66\x77\x88\x99\xaa"
                                  "\xbb\xcc",
                                  12),
                      {"  reg [71:0] v;", "$fscanf(fd, \"%u\", v)",
                       "v == 72'h99_88776655_44332211"},
                      f),
            "1 1\n");
}

TEST(ScanfDestinations, UnformattedFourValueFillsAWideTargetLowChunkFirst) {
  SimFixture f;
  std::string bytes;
  for (const char* chunk :
       {"\x11\x22\x33\x44", "\x55\x66\x77\x88", "\x99\xaa\xbb\xcc"}) {
    bytes += std::string(chunk, 4) + std::string(4, '\0');
  }
  EXPECT_EQ(ScanBytes("z72", bytes,
                      {"  logic [71:0] v;", "$fscanf(fd, \"%z\", v)",
                       "v === 72'h99_88776655_44332211"},
                      f),
            "1 1\n");
}

TEST(ScanfDestinations, UnformattedReadShortOfAWideTargetAssignsNoItem) {
  SimFixture f;
  std::string out =
      ScanBytes("short", std::string("\x11\x22\x33\x44\x55\x66\x77\x88", 8),
                {"  reg [71:0] v;", "$fscanf(fd, \"%u\", v)", "1'b1"}, f);
  EXPECT_NE(out.substr(0, 2), "1 ") << out;
}

TEST(ScanfDestinations, UnformattedCodesReadAStringOfBytesThroughSscanf) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [31:0] u;\n"
      "  logic [31:0] z;\n"
      "  integer n, m;\n"
      "  initial begin\n"
      "    n = $sscanf(32'h11223344, \"%u\", u);\n"
      "    m = $sscanf(64'h11223344_03010101, \"%z\", z);\n"
      "    $display(\"%0d %0d %0d %0d\", n, u == 32'h44332211, m,\n"
      "             z === 32'b0100_010z_0011_001x_0010_001z_0001_00zx);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1 1\n");
}

TEST(ScanfDestinations, FscanfDoesNotTreatANulByteAsWhiteSpace) {
  SimFixture f;
  EXPECT_EQ(
      ScanBytes("nul",
                std::string("7\0"
                            "8",
                            3),
                {"  integer a = 0, b = 99;", "$fscanf(fd, \"%d %d\", a, b)",
                 "$sformatf(\"%0d %0d\", a, b)"},
                f),
      "1 7 99\n");
}

TEST(ScanfDestinations, SscanfTreatsTheSameNulAsWhiteSpace) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer n, a = 0, b = 99;\n"
      "  initial begin\n"
      "    n = $sscanf(24'h370038, \"%d %d\", a, b);\n"
      "    $display(\"%0d %0d %0d\", n, a, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 7 8\n");
}

TEST(ScanfDestinations, DISABLED_ShortrealDestinationOverflowBecomesInfinity) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  shortreal a, b, c, d;\n"
      "  integer n;\n"
      "  initial begin\n"
      "    n = $sscanf(\"1e39 -1e39 1e400 -1e400\", \"%f %f %f %f\", a, b, c, "
      "d);\n"
      "    $display(\"%0d %g %g %g %g\", n, a, b, c, d);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 inf -inf inf -inf\n");
}

TEST(ScanfDestinations, RealtimeDestinationOverflowBecomesInfinity) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  realtime a, b;\n"
      "  integer n;\n"
      "  initial begin\n"
      "    n = $sscanf(\"1e400 -1e400\", \"%f %f\", a, b);\n"
      "    $display(\"%0d %g %g\", n, a, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 inf -inf\n");
}

}  // namespace
