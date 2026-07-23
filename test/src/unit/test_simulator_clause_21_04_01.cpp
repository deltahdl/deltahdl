// §21.4.1 Reading packed data — the $readmemb / $readmemh destinations this
// subclause adds on top of the §21.4 fixed unpacked array: unpacked arrays of
// packed data (each packed element handled as its vector equivalent), dynamic
// arrays and queues (whose current size is fixed for the load), and
// associative arrays (integral index only; loading an address creates the
// element, and an enumerated index is addressed by its members' numeric
// values).
//
// Every rule here is a runtime rule whose behavior depends on how the
// destination is produced: the element's packed shape (§7.4), a queue's
// declaration or push_back population (§7.10), a dynamic array's new[]
// sizing (§7.5), and an associative array's index type (§7.8, §6.19). These
// tests therefore declare each destination with its real syntax and drive the
// module through the full pipeline (parse -> elaborate -> lower -> run),
// reading the loaded elements back with $display — rather than hand-building
// container objects in an isolated evaluator.
#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Runs a single-module source through elaboration and simulation while
// capturing everything the run writes to stdout.
std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// Writes `data` to a scratch file tagged by `tag` and returns its path. The
// path contains no characters that need escaping inside a SystemVerilog
// string literal, so it can be embedded directly in the source under test.
std::string WriteData(const std::string& tag, const std::string& data) {
  std::string path = "/tmp/deltahdl_t210401_" + tag + ".mem";
  std::ofstream ofs(path);
  ofs << data;
  ofs.close();
  return path;
}

// ---------------------------------------------------------------------------
// Unpacked arrays of packed data: each packed element is handled as its
// vector equivalent, and the normal §21.4 operation is performed on it.
// ---------------------------------------------------------------------------

// §21.4.1: a packed-vector element wider than one file digit takes a whole
// multi-digit number as one word; nothing is split across elements.
TEST(ReadmemPackedDataSim, PackedVectorElementsLoadAsWholeWords) {
  SimFixture f;
  std::string path = WriteData("vec", "ABCD\n1234\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [15:0] mem [0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h\", mem[0], mem[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "abcd 1234\n");
  std::remove(path.c_str());
}

// §21.4.1: an element of a packed structure type is treated as the vector
// equivalent of the structure, so one file number fills the whole element.
TEST(ReadmemPackedDataSim, PackedStructElementsLoadAsVectorEquivalent) {
  SimFixture f;
  std::string path = WriteData("pstruct", "ABCD\n1234\n");
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct packed { logic [3:0] hi; logic [11:0] lo; } st_t;\n"
      "  st_t mem [0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h\", mem[0], mem[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "abcd 1234\n");
  std::remove(path.c_str());
}

// §21.4.1: a multidimensional packed element ([1:0][7:0]) is likewise one flat
// vector; the file number lands whole in the element, not per packed subword.
TEST(ReadmemPackedDataSim, MultiDimPackedElementsLoadAsFlatVectors) {
  SimFixture f;
  std::string path = WriteData("mdpacked", "ABCD\n1234\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [1:0][7:0] mem [0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h\", mem[0], mem[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "abcd 1234\n");
  std::remove(path.c_str());
}

// §21.4.1: a packed element wider than 64 bits still loads as one vector; the
// high words of the multi-word value survive intact.
TEST(ReadmemPackedDataSim, WidePackedElementLoadsAllWords) {
  SimFixture f;
  std::string path = WriteData("wide", "0123456789ABCDEF0123\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [79:0] mem [0:0];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h\", mem[0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "0123456789abcdef0123\n");
  std::remove(path.c_str());
}

// ---------------------------------------------------------------------------
// Dynamic arrays and queues: the current size of the array is fixed for the
// load, and the array shall not be resized.
// ---------------------------------------------------------------------------

// §21.4.1 (shall): a queue populated by push_back keeps its current size; a
// file holding more words than the queue has elements fills the existing
// elements and the surplus is dropped rather than appended.
TEST(ReadmemQueueDynSim, QueueSizeFixedSurplusWordsDropped) {
  SimFixture f;
  std::string path = WriteData("q_over", "0A\n14\n1E\n2A\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] q [$];\n"
      "  initial begin\n"
      "    q.push_back(8'h00); q.push_back(8'h00);\n"
      "    $readmemh(\"" +
          path +
          "\", q);\n"
          "    $display(\"%0d %h %h\", q.size(), q[0], q[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "2 0a 14\n");
  std::remove(path.c_str());
}

// §21.4.1: a queue declared with an assignment-pattern initializer loads into
// its existing elements; when the file is shorter than the queue, the tail
// elements keep their initializer values and the size does not change.
TEST(ReadmemQueueDynSim, QueueDeclInitTailUntouchedByShortFile) {
  SimFixture f;
  std::string path = WriteData("q_short", "11 22\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] q [$] = '{8'hEE, 8'hFF, 8'hDD};\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", q);\n"
          "    $display(\"%0d %h %h %h\", q.size(), q[0], q[1], q[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "3 11 22 dd\n");
  std::remove(path.c_str());
}

// §21.4.1: $readmemb loads a queue the same way, reading each number in
// binary; the destination container kind does not change the file grammar.
TEST(ReadmemQueueDynSim, ReadmembLoadsQueueInBinary) {
  SimFixture f;
  std::string path = WriteData("q_bin", "1010\n0110\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] q [$];\n"
      "  initial begin\n"
      "    q.push_back(8'h00); q.push_back(8'h00);\n"
      "    $readmemb(\"" +
          path +
          "\", q);\n"
          "    $display(\"%h %h\", q[0], q[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "0a 06\n");
  std::remove(path.c_str());
}

// §21.4.1 (shall): a dynamic array sized by a procedural new[] keeps that size
// through the load; a longer file does not grow it.
TEST(ReadmemQueueDynSim, DynamicArrayNewSizeIsFixed) {
  SimFixture f;
  std::string path = WriteData("dyn_new", "0A\n14\n1E\n2A\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] d [];\n"
      "  initial begin\n"
      "    d = new[3];\n"
      "    $readmemh(\"" +
          path +
          "\", d);\n"
          "    $display(\"%0d %h %h %h\", d.size(), d[0], d[1], d[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "3 0a 14 1e\n");
  std::remove(path.c_str());
}

// §21.4.1 (shall): the fixed-size rule also holds when the dynamic array is
// sized by a declaration initializer (= new[2]); the surplus file words are
// dropped and the size stays 2.
TEST(ReadmemQueueDynSim, DynamicArrayDeclInitNotResized) {
  SimFixture f;
  std::string path = WriteData("dyn_init", "11 22 33\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] d [] = new[2];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", d);\n"
          "    $display(\"%0d %h %h\", d.size(), d[0], d[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "2 11 22\n");
  std::remove(path.c_str());
}

// §21.4.1: a dynamic array sized by an assignment-pattern initializer keeps
// that size; a file shorter than the array fills the leading elements and the
// tail keeps its initializer value.
TEST(ReadmemQueueDynSim, DynamicArrayPatternInitTailUntouched) {
  SimFixture f;
  std::string path = WriteData("dyn_pat", "11 22\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] d [] = '{8'hEE, 8'hFF, 8'hDD};\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", d);\n"
          "    $display(\"%0d %h %h %h\", d.size(), d[0], d[1], d[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "3 11 22 dd\n");
  std::remove(path.c_str());
}

// §21.4.1 (shall): an @-address at or past the current size does not make
// room — the deposits are dropped, and the array keeps its size and contents.
TEST(ReadmemQueueDynSim, AddressPastCurrentSizeDoesNotGrowArray) {
  SimFixture f;
  std::string path = WriteData("dyn_past", "@4 AA BB\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] d [];\n"
      "  initial begin\n"
      "    d = new[2];\n"
      "    d[0] = 8'h01; d[1] = 8'h02;\n"
      "    $readmemh(\"" +
          path +
          "\", d);\n"
          "    $display(\"%0d %h %h\", d.size(), d[0], d[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "2 01 02\n");
  std::remove(path.c_str());
}

// ---------------------------------------------------------------------------
// Associative arrays: the index shall be integral; loading an address creates
// the element of that index when it does not already exist.
// ---------------------------------------------------------------------------

// §21.4.1: each @-address in the file names an integral key, and depositing a
// word there creates the element; unaddressed keys are not created.
TEST(ReadmemAssocSim, FileAddressesCreateElements) {
  SimFixture f;
  std::string path = WriteData("aa_addr", "@5 AB\n@10 CD\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [int];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", aa);\n"
          "    $display(\"%0d %h %h %0d %0d\", aa.num(), aa[5], aa[16],\n"
          "             aa.exists(5), aa.exists(6));\n"
          "  end\n"
          "endmodule\n",
      f);
  // @-addresses are hexadecimal, so @10 is key 16; key 6 was never loaded.
  EXPECT_EQ(out, "2 ab cd 1 0\n");
  std::remove(path.c_str());
}

// §21.4.1: with no address in the file the load starts at the default index 0
// and creates successive elements as the cursor advances.
TEST(ReadmemAssocSim, SequentialWordsCreateConsecutiveElements) {
  SimFixture f;
  std::string path = WriteData("aa_seq", "11 22 33\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [int];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", aa);\n"
          "    $display(\"%0d %h %h %h\", aa.num(), aa[0], aa[1], aa[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "3 11 22 33\n");
  std::remove(path.c_str());
}

// §21.4.1 / §21.4: a start_addr task argument (here supplied through an
// elaboration-time parameter) fixes the first created key; loading then
// advances upward, creating keys start, start+1, ...
TEST(ReadmemAssocSim, StartAddrParameterSetsFirstCreatedKey) {
  SimFixture f;
  std::string path = WriteData("aa_start", "11 22 33\n");
  std::string out = RunCapture(
      "module t;\n"
      "  parameter int START = 5;\n"
      "  logic [7:0] aa [int];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", aa, START);\n"
          "    $display(\"%0d %h %h %h\", aa.num(), aa[5], aa[6], aa[7]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "3 11 22 33\n");
  std::remove(path.c_str());
}

// §21.4.1 / §21.4: when start exceeds finish the created keys descend from the
// start address, following the load direction the task arguments fix.
TEST(ReadmemAssocSim, DescendingKeysWhenStartExceedsFinish) {
  SimFixture f;
  std::string path = WriteData("aa_desc", "11 22 33\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [int];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", aa, 9, 7);\n"
          "    $display(\"%0d %h %h %h\", aa.num(), aa[9], aa[8], aa[7]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "3 11 22 33\n");
  std::remove(path.c_str());
}

// §21.4.1: an element is created only when its index does not already exist —
// loading an existing key overwrites that element in place, and the cursor
// then advances to create genuinely new keys.
TEST(ReadmemAssocSim, ExistingElementOverwrittenNewKeysCreated) {
  SimFixture f;
  std::string path = WriteData("aa_upd", "@7 22 33\n@3 44\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [int];\n"
      "  initial begin\n"
      "    aa[7] = 8'h11;\n"
      "    $readmemh(\"" +
          path +
          "\", aa);\n"
          "    $display(\"%0d %h %h %h\", aa.num(), aa[7], aa[8], aa[3]);\n"
          "  end\n"
          "endmodule\n",
      f);
  // Key 7 pre-existed (overwritten 11 -> 22); keys 8 and 3 are created.
  EXPECT_EQ(out, "3 22 33 44\n");
  std::remove(path.c_str());
}

// §21.4.1: the wildcard index [*] admits any integral key, so it satisfies
// the integral-index requirement and loads like an int-indexed array.
TEST(ReadmemAssocSim, WildcardIndexLoadsAsIntegral) {
  SimFixture f;
  std::string path = WriteData("aa_wild", "11 22 33\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [*];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", aa);\n"
          "    $display(\"%0d %h %h %h\", aa.num(), aa[0], aa[1], aa[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "3 11 22 33\n");
  std::remove(path.c_str());
}

// §21.4.1 (shall): the index of a loaded associative array must be of an
// integral type. A string-keyed array has no numeric address form, so the
// load is rejected with an error and the array stays empty.
TEST(ReadmemAssocSim, StringIndexRejectedArrayUntouched) {
  SimFixture f;
  std::string path = WriteData("aa_str", "@1 AA\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [string];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", aa);\n"
          "    $display(\"after %0d\", aa.num());\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(out, "after 0\n");
  std::remove(path.c_str());
}

// ---------------------------------------------------------------------------
// Enumerated index types: address entries in the pattern file are numeric and
// correspond to the numeric values of the enumeration's elements (see 6.19).
// ---------------------------------------------------------------------------

// §21.4.1: with explicitly valued enum members, an @-address selects the
// member whose numeric value it equals; reading back through the member name
// finds the loaded word.
TEST(ReadmemAssocSim, EnumIndexAddressedByMemberValues) {
  SimFixture f;
  std::string path = WriteData("aa_enum", "@2 41\n@5 42\n");
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum {RED = 2, GREEN = 5} color_t;\n"
      "  logic [7:0] aa [color_t];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", aa);\n"
          "    $display(\"%0d %h %h\", aa.num(), aa[RED], aa[GREEN]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "2 41 42\n");
  std::remove(path.c_str());
}

// §21.4.1: with default-valued enum members (0, 1, 2, ...) a sequential file
// creates elements at the members' numeric values in declaration order.
TEST(ReadmemAssocSim, EnumIndexSequentialUsesDefaultValues) {
  SimFixture f;
  std::string path = WriteData("aa_enumseq", "11 22 33\n");
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum {A, B, C} abc_t;\n"
      "  logic [7:0] aa [abc_t];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", aa);\n"
          "    $display(\"%0d %h %h %h\", aa.num(), aa[A], aa[B], aa[C]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "3 11 22 33\n");
  std::remove(path.c_str());
}

}  // namespace
