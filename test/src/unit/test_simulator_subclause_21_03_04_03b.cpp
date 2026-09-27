#include <gtest/gtest.h>

#include <cstdio>
#include <string>

#include "fixture_simulator.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

// §21.3.4.3 (printed page 670) with §8.5 and §8.6: each converted field is
// stored in the argument after the format, in order, and a class property is
// such an argument -- through a handle, `$sscanf("word", "%s", r.s)` and
// `$fscanf(fd, "%d %s", r.n, r.w)`, or named bare inside one of the class's
// methods -- as is an element of an unpacked array.
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

}  // namespace
