#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

uint32_t RunAndCountWarnings(const std::string& src) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  return f.diag.WarningCount();
}

TEST(AssocArrayDeleteMethod, IntKeyByIndexRemovesOneEntry) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    aa.delete(10);\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayDeleteMethod, IntKeyByIndexKeepsOtherEntry) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    aa.delete(10);\n"
      "    result = aa[20];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 200u);
}

TEST(AssocArrayDeleteMethod, IntKeyByIndexDeletedKeyNoLongerExists) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    aa.delete(10);\n"
      "    result = aa.exists(10);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayDeleteMethod, IntKeyNoArgRemovesAllEntries) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    aa.delete();\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayDeleteMethod, IntKeyPropertySyntaxRemovesAllEntries) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    aa.delete;\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayDeleteMethod, NarrowIndexByIndexRemovesOneEntry) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[byte unsigned];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[50] = 1;\n"
      "    aa[200] = 2;\n"
      "    aa.delete(200);\n"
      "    result = aa[50];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayDeleteMethod, StringKeyByIndexRemovesOneEntry) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"hello\"] = 1;\n"
      "    map[\"world\"] = 2;\n"
      "    map.delete(\"hello\");\n"
      "    result = map.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayDeleteMethod, StringKeyByIndexKeepsOtherEntry) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"hello\"] = 1;\n"
      "    map[\"world\"] = 2;\n"
      "    map.delete(\"hello\");\n"
      "    result = map[\"world\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

TEST(AssocArrayDeleteMethod, StringKeyNoArgRemovesAllEntries) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"hello\"] = 1;\n"
      "    map[\"world\"] = 2;\n"
      "    map.delete();\n"
      "    result = map.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayDeleteMethod, WorkedExampleDeleteByKeyLeavesTwo) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"hello\"] = 1;\n"
      "    map[\"sad\"] = 2;\n"
      "    map[\"world\"] = 3;\n"
      "    map.delete(\"sad\");\n"
      "    result = map.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

TEST(AssocArrayDeleteMethod, WorkedExampleDeleteAllEmptiesMap) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"hello\"] = 1;\n"
      "    map[\"sad\"] = 2;\n"
      "    map[\"world\"] = 3;\n"
      "    map.delete;\n"
      "    result = map.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayDeleteMethod, MissingIntKeyLeavesContentsUnchanged) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa.delete(999);\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayDeleteMethod, IntKeyByVariableIndexRemovesTargetedEntry) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int key;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    key = 10;\n"
      "    aa.delete(key);\n"
      "    result = aa.exists(10);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayDeleteMethod, StringKeyByVariableIndexRemovesTargetedEntry) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string k;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"hello\"] = 1;\n"
      "    map[\"world\"] = 2;\n"
      "    k = \"hello\";\n"
      "    map.delete(k);\n"
      "    result = map.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayDeleteMethod, MissingIntKeyIssuesNoWarning) {
  uint32_t baseline = RunAndCountWarnings(
      "module t;\n"
      "  int aa[int];\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "  end\n"
      "endmodule\n");
  uint32_t with_delete = RunAndCountWarnings(
      "module t;\n"
      "  int aa[int];\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa.delete(999);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(with_delete, baseline);
  EXPECT_EQ(with_delete, 0u);
}

TEST(AssocArrayDeleteMethod, MissingStringKeyIssuesNoWarning) {
  uint32_t baseline = RunAndCountWarnings(
      "module t;\n"
      "  int map[string];\n"
      "  initial begin\n"
      "    map[\"hello\"] = 1;\n"
      "  end\n"
      "endmodule\n");
  uint32_t with_delete = RunAndCountWarnings(
      "module t;\n"
      "  int map[string];\n"
      "  initial begin\n"
      "    map[\"hello\"] = 1;\n"
      "    map.delete(\"missing\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(with_delete, baseline);
  EXPECT_EQ(with_delete, 0u);
}

TEST(AssocArrayDeleteMethod,
     DeleteOnAHandleArrayPropertyInATaskReportsNothing) {
  SimFixture f;
  auto out = RunCapture(
      "class E; endclass\n"
      "class K; endclass\n"
      "class O;\n"
      "  E m_events[K];\n"
      "  task drop(K k);\n"
      "    m_events[k] = new;\n"
      "    m_events.delete(k);\n"
      "    $display(\"num=%0d\", m_events.num());\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static O o = new;\n"
      "    static K k = new;\n"
      "    o.drop(k);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "num=0\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
