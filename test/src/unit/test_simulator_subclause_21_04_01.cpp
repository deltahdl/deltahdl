#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string WriteData(const std::string& tag, const std::string& data) {
  std::string path = "/tmp/deltahdl_t210401_" + tag + ".mem";
  std::ofstream ofs(path);
  ofs << data;
  ofs.close();
  return path;
}

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
  EXPECT_EQ(out, "2 ab cd 1 0\n");
  std::remove(path.c_str());
}

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
  EXPECT_EQ(out, "3 22 33 44\n");
  std::remove(path.c_str());
}

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$readmemh: associative array index must be of an integral type", 4,
      "21.4.1"));
  EXPECT_EQ(out, "after 0\n");
  std::remove(path.c_str());
}

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

TEST(ReadmemAssocSim, StringIndexRejectionNames21_4_1) {
  SimFixture f;
  std::string path = WriteData("aa_sub", "@2 BB\n");
  RunCapture(
      "module t;\n"
      "  logic [7:0] aa [string];\n"
      "  initial $readmemh(\"" +
          path +
          "\", aa);\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "associative array index must be of an integral type", 3, "21.4.1"));
  std::remove(path.c_str());
}

}  // namespace
