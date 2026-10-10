#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §7.8.5: an index of a user-defined type is keyed by its whole value, so two
// structures that differ only in a member lying above bit 63 of the
// structure's 80 bits are two entries.
TEST(UserDefinedIndexAssocArraySimulation,
     StructureIndexIsKeyedByItsWholeValue) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct packed { bit [15:0] hi; bit [63:0] lo; } k_t;\n"
      "  int m [k_t];\n"
      "  k_t a, b;\n"
      "  initial begin\n"
      "    a = '{hi: 1, lo: 0};\n"
      "    b = '{hi: 2, lo: 0};\n"
      "    m[a] = 1;\n"
      "    m[b] = 2;\n"
      "    $display(\"%0d %0d %0d\", m.num(), m[a], m[b]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 1 2\n");
}

}  // namespace
