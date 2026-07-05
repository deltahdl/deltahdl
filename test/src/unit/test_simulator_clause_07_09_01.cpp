// Tests for IEEE 1800-2023 clause 7.9.1 -- the num() and size() associative
// array methods. Both return the number of entries currently in the array,
// and both return 0 when the array is empty. Because that count is produced by
// element allocation on write (clause 7.8, this pass's dependency), every test
// builds the array from real declaration + indexed-assignment source and drives
// it through parse -> elaborate -> lower -> run, observing the value the method
// hands back rather than hand-building the array object.

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// The clause 7.9.1 worked example: an int-keyed array populated with three
// distinct keys reports num() == 3.
TEST(AssocArrayNumSizeMethods, NumReturnsEntryCount_IntKeyed) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int imem[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    imem[ 3 ] = 1;\n"
      "    imem[ 16'hffff ] = 2;\n"
      "    imem[ 4'b1000 ] = 3;\n"
      "    result = imem.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

// size() is an alias for num(): same array, same count.
TEST(AssocArrayNumSizeMethods, SizeReturnsEntryCount_IntKeyed) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int imem[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    imem[ 3 ] = 1;\n"
      "    imem[ 16'hffff ] = 2;\n"
      "    imem[ 4'b1000 ] = 3;\n"
      "    result = imem.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

// The clause 7.9.1 example writes `imem.num` with no parentheses; the method
// call is also valid as a property reference.
TEST(AssocArrayNumSizeMethods, NumPropertyFormNoParens) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int imem[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    imem[ 3 ] = 1;\n"
      "    imem[ 16'hffff ] = 2;\n"
      "    imem[ 4'b1000 ] = 3;\n"
      "    result = imem.num;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(AssocArrayNumSizeMethods, SizePropertyFormNoParens) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int imem[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    imem[ 3 ] = 1;\n"
      "    imem[ 16'hffff ] = 2;\n"
      "    result = imem.size;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

// The count is over entries regardless of the index (key) data type: a
// string-keyed array reports its live entry count just the same.
TEST(AssocArrayNumSizeMethods, NumReturnsEntryCount_StringKeyed) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"hello\"] = 1;\n"
      "    map[\"world\"] = 2;\n"
      "    result = map.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

TEST(AssocArrayNumSizeMethods, SizeReturnsEntryCount_StringKeyed) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"hello\"] = 1;\n"
      "    map[\"world\"] = 2;\n"
      "    map[\"again\"] = 3;\n"
      "    result = map.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

// Empty array: both methods return 0. This is the rule's boundary case and the
// closest thing to a "reject" -- nothing has been allocated, so the count is 0
// rather than any nonzero value.
TEST(AssocArrayNumSizeMethods, NumReturnsZeroForEmptyIntKeyed) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int imem[int];\n"
      "  int result;\n"
      "  initial result = imem.num();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayNumSizeMethods, SizeReturnsZeroForEmptyStringKeyed) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  int result;\n"
      "  initial result = map.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// "Number of entries" counts distinct keys: overwriting an existing key is a
// write to the same entry (clause 7.8), so the count does not grow.
TEST(AssocArrayNumSizeMethods, CountIsDistinctKeysNotWrites) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int imem[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    imem[ 7 ] = 1;\n"
      "    imem[ 7 ] = 2;\n"
      "    imem[ 7 ] = 3;\n"
      "    result = imem.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// num() and size() are aliases: on the same populated array they agree.
TEST(AssocArrayNumSizeMethods, NumEqualsSize) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int imem[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    imem[ 100 ] = 1;\n"
      "    imem[ 200 ] = 2;\n"
      "    imem[ 300 ] = 3;\n"
      "    imem[ 400 ] = 4;\n"
      "    result = (imem.num() == imem.size());\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

}  // namespace
