#include <gtest/gtest.h>

#include <cstdio>
#include <string>

#include "fixture_simulator.h"
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

}  // namespace
