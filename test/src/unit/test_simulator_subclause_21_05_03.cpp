#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

TEST(WritememAddressSim, UnpackedArrayNoAddressSpecifiers) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_unp.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  logic [7:0] dst [0:3];\n"
      "  initial begin\n"
      "    mem[0] = 8'h11; mem[1] = 8'h22; mem[2] = 8'h33; mem[3] = 8'h44;\n"
      "    $writememh(\"" +
          path +
          "\", mem);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%h %h %h %h\", dst[0], dst[1], dst[2], dst[3]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "11 22 33 44\n");
  std::string contents = SlurpFile(path);
  EXPECT_EQ(contents, "11\n22\n33\n44\n");
  EXPECT_EQ(contents.find('@'), std::string::npos);
  std::remove(path.c_str());
}

TEST(WritememAddressSim, UnpackedArrayBinaryDumpBare) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_unpb.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] mem [0:1];\n"
      "  initial begin\n"
      "    mem[0] = 8'h11; mem[1] = 8'h22;\n"
      "    $writememb(\"" +
          path +
          "\", mem);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  std::string contents = SlurpFile(path);
  EXPECT_EQ(contents, "00010001\n00100010\n");
  EXPECT_EQ(contents.find('@'), std::string::npos);
  std::remove(path.c_str());
}

TEST(WritememAddressSim, DescendingDeclArrayDumpedBare) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_desc.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] mem [3:0];\n"
      "  initial begin\n"
      "    mem[0] = 8'hA0; mem[1] = 8'hA1; mem[2] = 8'hA2; mem[3] = 8'hA3;\n"
      "    $writememh(\"" +
          path +
          "\", mem);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  std::string contents = SlurpFile(path);
  EXPECT_EQ(contents, "a0\na1\na2\na3\n");
  EXPECT_EQ(contents.find('@'), std::string::npos);
  std::remove(path.c_str());
}

TEST(WritememAddressSim, BoundedWindowStillNoAddressSpecifiers) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_win.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    mem[0] = 8'h11; mem[1] = 8'h22; mem[2] = 8'h33; mem[3] = 8'h44;\n"
      "    $writememh(\"" +
          path +
          "\", mem, 1, 2);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  std::string contents = SlurpFile(path);
  EXPECT_EQ(contents, "22\n33\n");
  EXPECT_EQ(contents.find('@'), std::string::npos);
  std::remove(path.c_str());
}

TEST(WritememAddressSim, DynamicArrayNoAddressSpecifiers) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_dyn.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] d [];\n"
      "  logic [7:0] r [];\n"
      "  initial begin\n"
      "    d = new[2]; d[0] = 8'hAB; d[1] = 8'hCD;\n"
      "    $writememh(\"" +
          path +
          "\", d);\n"
          "    r = new[2];\n"
          "    $readmemh(\"" +
          path +
          "\", r);\n"
          "    $display(\"%h %h\", r[0], r[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "ab cd\n");
  std::string contents = SlurpFile(path);
  EXPECT_EQ(contents, "ab\ncd\n");
  EXPECT_EQ(contents.find('@'), std::string::npos);
  std::remove(path.c_str());
}

TEST(WritememAddressSim, QueueDumpedBare) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_q.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  byte q [$];\n"
      "  initial begin\n"
      "    q.push_back(8'h0F); q.push_back(8'hF0);\n"
      "    $writememb(\"" +
          path +
          "\", q);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  std::string contents = SlurpFile(path);
  EXPECT_EQ(contents, "00001111\n11110000\n");
  EXPECT_EQ(contents.find('@'), std::string::npos);
  std::remove(path.c_str());
}

TEST(WritememAddressSim, MultiDimUnpackedArrayDumpedBare) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_md.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] m [0:1][0:1];\n"
      "  initial begin\n"
      "    m[0][0] = 8'h11; m[0][1] = 8'h22;\n"
      "    m[1][0] = 8'h33; m[1][1] = 8'h44;\n"
      "    $writememh(\"" +
          path +
          "\", m);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  std::string contents = SlurpFile(path);
  EXPECT_EQ(contents, "11\n22\n33\n44\n");
  EXPECT_EQ(contents.find('@'), std::string::npos);
  std::remove(path.c_str());
}

TEST(WritememAddressSim, AssocArrayAddressSpecifiersWritten) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_aa.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [int];\n"
      "  logic [7:0] bb [int];\n"
      "  initial begin\n"
      "    aa[5] = 8'hAB; aa[16] = 8'hCD;\n"
      "    $writememh(\"" +
          path +
          "\", aa);\n"
          "    $readmemh(\"" +
          path +
          "\", bb);\n"
          "    $display(\"%0d %h %h\", bb.num(), bb[5], bb[16]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "2 ab cd\n");
  EXPECT_EQ(SlurpFile(path), "@5\nab\n@10\ncd\n");
  std::remove(path.c_str());
}

TEST(WritememAddressSim, AssocArrayBinaryDumpHasAddresses) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_aab.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [int];\n"
      "  initial begin\n"
      "    aa[5] = 8'hAB; aa[16] = 8'hCD;\n"
      "    $writememb(\"" +
          path +
          "\", aa);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  EXPECT_EQ(SlurpFile(path), "@5\n10101011\n@10\n11001101\n");
  std::remove(path.c_str());
}

TEST(WritememAddressSim, AssocTypedefVectorIndexDumpsAddresses) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_vec.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  typedef bit [15:0] addr_t;\n"
      "  logic [7:0] aa [addr_t];\n"
      "  initial begin\n"
      "    aa[16'h20] = 8'h77;\n"
      "    $writememh(\"" +
          path +
          "\", aa);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  EXPECT_EQ(SlurpFile(path), "@20\n77\n");
  std::remove(path.c_str());
}

TEST(WritememAddressSim, AssocWildcardIndexDumpsAddresses) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_wild.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [*];\n"
      "  initial begin\n"
      "    aa[9] = 8'h99;\n"
      "    $writememh(\"" +
          path +
          "\", aa);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  EXPECT_EQ(SlurpFile(path), "@9\n99\n");
  std::remove(path.c_str());
}

std::string DumpAssoc(const std::string& path, const std::string& decl,
                      const std::string& stores) {
  SimFixture f;
  RunCapture("module t;\n" + decl + "  initial begin\n" + stores +
                 "    $writememh(\"" + path + "\", aa);\n  end\nendmodule\n",
             f);
  std::string text = SlurpFile(path);
  std::remove(path.c_str());
  return text;
}

TEST(WritememAddressSim, AssocIndexWiderThan64BitsKeepsHighBits) {
  EXPECT_EQ(DumpAssoc("/tmp/deltahdl_t210503_w80.mem",
                      "  typedef bit [79:0] wide_t;\n"
                      "  logic [7:0] aa [wide_t];\n",
                      "    aa[80'h1_0000_0000_0000_0001] = 8'hab;\n"
                      "    aa[1] = 8'hcd;\n"),
            "@1\ncd\n@10000000000000001\nab\n");
}

TEST(WritememAddressSim, AssocNegativeIntIndexWrittenAtIndexWidth) {
  EXPECT_EQ(
      DumpAssoc("/tmp/deltahdl_t210503_neg.mem", "  logic [7:0] aa [int];\n",
                "    aa[-1] = 8'h11;\n    aa[2] = 8'h22;\n"),
      "@ffffffff\n11\n@2\n22\n");
}

TEST(WritememAddressSim, AssocWildcardIndexWiderThan64BitsKeepsHighBits) {
  EXPECT_EQ(
      DumpAssoc("/tmp/deltahdl_t210503_w72.mem", "  logic [7:0] aa [*];\n",
                "    aa[72'h1_0000_0000_0000_0002] = 8'h5a;\n"),
      "@10000000000000002\n5a\n");
}

TEST(WritememAddressSim, AssocEnumIndexNumericAddresses) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_enum.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum {RED = 2, GREEN = 5} color_t;\n"
      "  logic [7:0] aa [color_t];\n"
      "  logic [7:0] bb [int];\n"
      "  initial begin\n"
      "    aa[RED] = 8'h41; aa[GREEN] = 8'h42;\n"
      "    $writememh(\"" +
          path +
          "\", aa);\n"
          "    $readmemh(\"" +
          path +
          "\", bb);\n"
          "    $display(\"%0d %h %h\", bb.num(), bb[2], bb[5]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "2 41 42\n");
  EXPECT_EQ(SlurpFile(path), "@2\n41\n@5\n42\n");
  std::remove(path.c_str());
}

TEST(WritememAddressSim, TaskBodyCallWritesAddresses) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_task.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [int];\n"
      "  task dump_aa;\n"
      "    $writememh(\"" +
          path +
          "\", aa);\n"
          "  endtask\n"
          "  initial begin\n"
          "    aa[5] = 8'hAB; aa[16] = 8'hCD;\n"
          "    dump_aa;\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  EXPECT_EQ(SlurpFile(path), "@5\nab\n@10\ncd\n");
  std::remove(path.c_str());
}

TEST(WritememAddressSim, StringIndexRejectedFileUntouched) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_str.mem";
  {
    std::ofstream pre(path);
    pre << "KEEP\n";
  }
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [string];\n"
      "  initial begin\n"
      "    $writememh(\"" +
          path +
          "\", aa);\n"
          "    $display(\"after\");\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$writememh: associative array index must be of an integral type", 4,
      "21.5.3"));
  EXPECT_EQ(out, "after\n");
  EXPECT_EQ(SlurpFile(path), "KEEP\n");
  std::remove(path.c_str());
}

TEST(WritememAddressSim, StringIndexRejectedWritememb) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_strb.mem";
  std::remove(path.c_str());
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [string];\n"
      "  initial begin\n"
      "    $writememb(\"" +
          path +
          "\", aa);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$writememb: associative array index must be of an integral type", 4,
      "21.5.3"));
  EXPECT_EQ(out, "");
  std::ifstream check(path);
  EXPECT_FALSE(check.good());
  std::remove(path.c_str());
}

TEST(WritememAddressSim, StringIndexRejectionNames21_5_3) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_sub.mem";
  RunCapture(
      "module t;\n"
      "  logic [7:0] aa [string];\n"
      "  initial $writememh(\"" +
          path +
          "\", aa);\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "associative array index must be of an integral type", 3, "21.5.3"));
  std::remove(path.c_str());
}

}  // namespace
