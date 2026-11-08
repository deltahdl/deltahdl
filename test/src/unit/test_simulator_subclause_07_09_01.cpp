#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

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
      "    static srv o = new;\n"
      "    o.reset_severity_counts();\n"
      "    result = o.count();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

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
      "    static C c = new;\n"
      "    c.fill();\n"
      "    result = c.count();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5u);
}

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
      "    static C c = new;\n"
      "    c.fill();\n"
      "    result = c.imem.size() * 10;\n"
      "    c.imem[3] = 30;\n"
      "    result = result + c.imem.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 23u);
}

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
      "    static C c = new;\n"
      "    result = c.fill();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

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
      "    static C c = new;\n"
      "    result = c.fill();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

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
      "    static C a = new;\n"
      "    static C b = new;\n"
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
