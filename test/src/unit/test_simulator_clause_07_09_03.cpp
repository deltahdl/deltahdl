// Tests for IEEE 1800-2023 clause 7.9.3 -- the exists() associative array
// method. exists() checks whether an element is present at the given index and
// returns 1 if so, otherwise 0. Whether an entry is present is determined by
// prior element allocation on write (clause 7.8, this pass's dependency), so
// every test builds the array from real declaration + indexed-assignment source
// and drives it through parse -> elaborate -> lower -> run, observing the value
// exists() hands back rather than hand-building the array object. The index is
// supplied through each dependency's real key syntax: integral keys (7.8.4) and
// string keys (7.8.2).

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// A present integral index reports exists() == 1. The key is allocated by the
// indexed write, then queried by value.
TEST(AssocArrayExistsMethod, ReturnsOneForPresentIntKey) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    result = aa.exists(10);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// An index never written reports exists() == 0 -- the "not present" path.
TEST(AssocArrayExistsMethod, ReturnsZeroForMissingIntKey) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    result = aa.exists(999);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// The membership test is independent of the index data type: a string-keyed
// array (dependency 7.8.2) reports a present key just the same.
TEST(AssocArrayExistsMethod, ReturnsOneForPresentStringKey) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"hello\"] = 1;\n"
      "    result = map.exists(\"hello\");\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayExistsMethod, ReturnsZeroForMissingStringKey) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"hello\"] = 1;\n"
      "    result = map.exists(\"missing\");\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// Wildcard index type (dependency 7.8.1): exists() reports a present key. The
// key is allocated by the indexed write and then probed by value.
TEST(AssocArrayExistsMethod, ReturnsOneForPresentWildcardKey) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[*];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[5] = 77;\n"
      "    result = aa.exists(5);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayExistsMethod, ReturnsZeroForMissingWildcardKey) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[*];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[5] = 77;\n"
      "    result = aa.exists(6);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// Class index type (dependency 7.8.3): the index is a class handle produced by
// a real 'new'. exists() reports the handle under which a value was stored.
TEST(AssocArrayExistsMethod, ReturnsOneForPresentClassHandleKey) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "  int result;\n"
      "  initial begin\n"
      "    Foo k;\n"
      "    k = new;\n"
      "    data[k] = 55;\n"
      "    result = data.exists(k);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// A distinct handle from a separate 'new' is a different key, so exists()
// reports 0 for a handle under which nothing was stored.
TEST(AssocArrayExistsMethod, ReturnsZeroForMissingClassHandleKey) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "  int result;\n"
      "  initial begin\n"
      "    Foo a, b;\n"
      "    a = new;\n"
      "    b = new;\n"
      "    data[a] = 10;\n"
      "    result = data.exists(b);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// Boundary case: querying an array into which nothing has been written yields
// 0.
TEST(AssocArrayExistsMethod, ReturnsZeroForEmptyArray) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial result = aa.exists(0);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// exists() is a query: unlike a read or write access (clause 7.8.7), probing an
// absent index does not allocate an entry. After a false exists() on a key that
// was never written, the array's live entry count is unchanged.
TEST(AssocArrayExistsMethod, AbsentQueryDoesNotAllocate) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  int probe;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    probe = aa.exists(99);\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// The clause 7.9.3 worked example, present-key path: because "hello" exists,
// the then-branch runs and increments the entry.
TEST(AssocArrayExistsMethod, IfConditionTakesThenBranchWhenPresent) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"hello\"] = 5;\n"
      "    if (map.exists(\"hello\"))\n"
      "      map[\"hello\"] += 1;\n"
      "    else\n"
      "      map[\"hello\"] = 0;\n"
      "    result = map[\"hello\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 6u);
}

// The clause 7.9.3 worked example, absent-key path: "hello" does not exist, so
// exists() is false and the else-branch runs, seeding the entry with 0.
TEST(AssocArrayExistsMethod, IfConditionTakesElseBranchWhenAbsent) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    if (map.exists(\"hello\"))\n"
      "      map[\"hello\"] += 1;\n"
      "    else\n"
      "      map[\"hello\"] = 7;\n"
      "    result = map[\"hello\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

}  // namespace
