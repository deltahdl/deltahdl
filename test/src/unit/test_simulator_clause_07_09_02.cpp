// Tests for IEEE 1800-2023 clause 7.9.2 -- the delete() associative array
// method. delete(index) removes the single entry stored under that index;
// delete() with no argument (and the parenless property form `aa.delete;`)
// removes every entry; deleting an index that is not present is a silent no-op
// that issues no warning. Every one of those behaviors acts on entries that
// were produced by prior indexed writes (clause 7.8, this pass's dependency)
// and, for delete(index), on an index value passed by value (clause 13.5.1),
// so each test builds the array from real declaration + indexed-assignment
// source and drives it through parse -> elaborate -> lower -> run, observing
// the surviving contents through a witness variable (num()/exists()/an element
// read) rather than hand-building the array object. Because delete() returns
// void, the effect is always read back from real source after the deletion.
// The index type is supplied through each dependency's real key syntax:
// integral keys (7.8.4) and string keys (7.8.2).

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// Drives real source through the full pipeline and reports how many warnings
// the run produced. Used to observe the clause 7.9.2 rule that deleting an
// absent index issues no warning: the count must stay at zero across such a
// delete. Mirrors RunAndGet but exposes the fixture's diagnostic tally.
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

// delete(index) on an integral-keyed array removes just the named entry: after
// deleting one of two keys, num() reports a single surviving entry.
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

// delete(index) removes the *targeted* entry and no other: the untouched key
// still yields its stored value after the deletion.
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

// After delete(index), the deleted key no longer exists: exists() returns 0.
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

// delete() with no argument removes every entry of an integral-keyed array.
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

// The parenless property form `aa.delete;` also removes every entry.
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

// A narrow integral index type (dependency 7.8.4) still selects the right entry
// to delete: after deleting key 200, only key 50 survives.
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

// String-keyed (dependency 7.8.2): delete(index) removes just the named key,
// leaving the other entry countable.
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

// String-keyed delete(index) leaves the non-targeted key's value intact.
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

// String-keyed delete() with no argument removes every entry.
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

// The clause 7.9.2 worked example, delete-by-key half: a string-keyed map with
// three entries, after map.delete("sad"), retains two entries.
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

// The clause 7.9.2 worked example, delete-all half: after the parenless
// map.delete;, the map is empty.
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

// Deleting a key that is not present is a no-op on the contents: the existing
// entries survive untouched.
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

// The index argument is passed by value (dependency 13.5.1): when the key to
// delete is supplied through a real integral variable rather than a literal,
// delete() still removes exactly that entry. The variable is declared and
// assigned from source and consumed as the actual argument, driving the
// by-value argument path end to end.
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

// The same by-value argument path (dependency 13.5.1) with a string key
// supplied through a string variable: after the delete, only the untouched
// entry remains.
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

// §7.9.2: deleting an integral index that does not exist issues no warning.
// Isolated differentially: the same module without the delete and with the
// missing-key delete must emit the identical (zero) warning count, so the
// no-op delete contributes nothing to the diagnostic tally.
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

// §7.9.2: deleting a string index that does not exist likewise issues no
// warning, isolated the same differential way.
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

}  // namespace
