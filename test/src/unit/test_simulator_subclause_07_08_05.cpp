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

// §7.8.5 with §6.14: a chandle is a legal index type, and a chandle variable
// starts as null, so the entry written under `h` is read back under it and is
// the array's one entry. The array was built with no dimension, so `m[h]`
// selected nothing.
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

// §7.8.5 with §15.5.5.3: an event index keys an entry by the object the event
// refers to, so two events are two entries and `null` a third. Once `e2 = e1`
// merges them (§15.5.5.1), e2 refers to e1's object and reads e1's entry.
// Every event read as one bit, so e1 and e2 shared an entry.
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
