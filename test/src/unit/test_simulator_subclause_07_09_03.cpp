#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

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

TEST(AssocArrayExistsMethod, ReportsTheKeyAClassMethodWroteAndNotAnother) {
  uint64_t v = RunAndGet(
      "package p;\n"
      "  typedef enum { UVM_INFO, UVM_WARNING, UVM_ERROR, UVM_FATAL }\n"
      "    uvm_severity;\n"
      "  class srv;\n"
      "    int m_severity_count[uvm_severity];\n"
      "    function int probe();\n"
      "      m_severity_count[UVM_ERROR] = 1;\n"
      "      return m_severity_count.exists(UVM_ERROR) * 10 +\n"
      "             m_severity_count.exists(UVM_FATAL);\n"
      "    endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "import p::*;\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    static srv o = new;\n"
      "    result = o.probe();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 10u);
}

TEST(AssocArrayExistsMethod, ReportsThroughAHandleTheKeysAClassPropertyHolds) {
  uint64_t v = RunAndGet(
      "class C;\n"
      "  int aa[string];\n"
      "  function void fill();\n"
      "    aa[\"hello\"] = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.fill();\n"
      "    c.aa[\"world\"] = 2;\n"
      "    result = c.aa.exists(\"hello\") * 100 + c.aa.exists(\"world\") * 10 "
      "+\n"
      "             c.aa.exists(\"sad\");\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 110u);
}

}  // namespace
