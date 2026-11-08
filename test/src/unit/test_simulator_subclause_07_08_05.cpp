#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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

TEST(UserDefinedIndexAssocArraySimulation, ChandleIndexKeysAnEntry) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int m [chandle];\n"
      "  chandle h;\n"
      "  initial begin\n"
      "    m[h] = 7;\n"
      "    $display(\"%0d %0d %0d\", m.num(), m[h], m.exists(h));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 7 1\n");
}

TEST(UserDefinedIndexAssocArraySimulation, EventIndexKeysByTheObject) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int b [event];\n"
      "  event e1, e2;\n"
      "  initial begin\n"
      "    b[e1] = 1;\n"
      "    b[e2] = 2;\n"
      "    b[null] = 3;\n"
      "    $display(\"%0d %0d %0d %0d\", b[e1], b[e2], b[null], b.num());\n"
      "    e2 = e1;\n"
      "    $display(\"%0d\", b[e2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 3 3\n1\n");
}

}  // namespace
