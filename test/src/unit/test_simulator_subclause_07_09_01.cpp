// Tests for IEEE 1800-2023 clause 7.9.1 -- the num() and size() associative
// array methods. Both return the number of entries currently in the array,
// and both return 0 when the array is empty. Because that count is produced by
// element allocation on write (clause 7.8, this pass's dependency), every test
// builds the array from real declaration + indexed-assignment source and drives
// it through parse -> elaborate -> lower -> run, observing the value the method
// hands back rather than hand-building the array object.

#include <gtest/gtest.h>

#include <cstdint>

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

// §7.9.1 counts the entries of the array whatever names it, and §8.5 puts no
// restriction on a class property's type, so a property declared with an
// associative dimension is an associative array of the object. This is
// uvm_report_server::reset_severity_counts: a method of the class writes one
// entry per member of the enumeration keying the array, and size() counts the
// four. An element write to the property went nowhere before -- no writer
// knew the property as an array -- so the count read 0.
TEST(AssocArrayNumSizeMethods, SizeCountsTheEnumKeyedEntriesAClassMethodWrote) {
  uint64_t v = RunAndGet(
      "package p;\n"
      "  typedef enum { UVM_INFO, UVM_WARNING, UVM_ERROR, UVM_FATAL }\n"
      "    uvm_severity;\n"
      "  class srv;\n"
      "    int m_severity_count[uvm_severity];\n"
      "    function void reset_severity_counts();\n"
      "      uvm_severity s;\n"
      "      s = s.first();\n"
      "      forever begin\n"
      "        m_severity_count[s] = 0;\n"
      "        if (s == s.last()) break;\n"
      "        s = s.next();\n"
      "      end\n"
      "    endfunction\n"
      "    function int count();\n"
      "      return m_severity_count.size();\n"
      "    endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "import p::*;\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    srv o = new;\n"
      "    o.reset_severity_counts();\n"
      "    result = o.count();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

// An int-keyed property written by a method counts its distinct keys, as
// §7.9.1's own example does for a declared array: five keys, one of them
// written twice, make five entries.
TEST(AssocArrayNumSizeMethods, NumCountsTheIntKeyedEntriesAClassMethodWrote) {
  uint64_t v = RunAndGet(
      "class C;\n"
      "  int imem[int];\n"
      "  function void fill();\n"
      "    imem[3] = 1;\n"
      "    imem[16'hffff] = 2;\n"
      "    imem[4'b1000] = 3;\n"
      "    imem[-7] = 4;\n"
      "    imem[100] = 5;\n"
      "    imem[3] = 6;\n"
      "  endfunction\n"
      "  function int count();\n"
      "    return imem.num();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    c.fill();\n"
      "    result = c.count();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5u);
}

// §8.5: the property is reached through the instance too, so size() called
// on `c.imem` from the module counts what the method wrote, and an element
// written through the handle joins the count.
TEST(AssocArrayNumSizeMethods, SizeThroughAHandleCountsEntriesOfTheProperty) {
  uint64_t v = RunAndGet(
      "class C;\n"
      "  int imem[int];\n"
      "  function void fill();\n"
      "    imem[1] = 10;\n"
      "    imem[2] = 20;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    c.fill();\n"
      "    result = c.imem.size() * 10;\n"
      "    c.imem[3] = 30;\n"
      "    result = result + c.imem.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 23u);
}

// §7.9.1's parenthesis-free `imem.num` reads the property's count inside a
// method as it reads a declared array's.
TEST(AssocArrayNumSizeMethods, NumPropertyFormCountsAClassPropertysEntries) {
  uint64_t v = RunAndGet(
      "class C;\n"
      "  int smem[string];\n"
      "  function int fill();\n"
      "    smem[\"hello\"] = 1;\n"
      "    smem[\"sad\"] = 2;\n"
      "    smem[\"world\"] = 3;\n"
      "    return smem.num;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    result = c.fill();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

// §7.9.1 with §7.9.2: delete(index) on the property removes the one entry, so
// three written and one deleted count two.
TEST(AssocArrayNumSizeMethods, SizeCountsAClassPropertysEntriesAfterADelete) {
  uint64_t v = RunAndGet(
      "class C;\n"
      "  int imem[int];\n"
      "  function int fill();\n"
      "    imem[5] = 1;\n"
      "    imem[6] = 2;\n"
      "    imem[7] = 3;\n"
      "    imem.delete(6);\n"
      "    return imem.size();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    result = c.fill();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

// §8.9: a static property declared with an associative dimension is one array
// shared by every instance, so the keys two objects write are counted
// together from either.
TEST(AssocArrayNumSizeMethods,
     SizeCountsAStaticClassPropertysEntriesFromAnyInstance) {
  uint64_t v = RunAndGet(
      "class C;\n"
      "  static int tbl[string];\n"
      "  function void add(string k);\n"
      "    tbl[k] = 1;\n"
      "  endfunction\n"
      "  function int count();\n"
      "    return tbl.size();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C a = new;\n"
      "    C b = new;\n"
      "    a.add(\"x\");\n"
      "    b.add(\"y\");\n"
      "    b.add(\"x\");\n"
      "    result = a.count();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

}  // namespace
