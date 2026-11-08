#include <gtest/gtest.h>

#include <cstdint>
#include <cstdio>
#include <fstream>
#include <string>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string WritePersonalityFile(const std::string& tag,
                                 const std::string& data) {
  std::string path = "/tmp/deltahdl_t201604_" + tag + ".mem";
  std::ofstream ofs(path);
  ofs << data;
  ofs.close();
  return path;
}

TEST(PlaPersonalityFormat, ArrayFormatOneTakesInputZeroExcludesIt) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  initial begin\n"
                           "    mem[1] = 2'b10;\n"
                           "    in = 2'b10;\n"
                           "    $sync$and$array(mem, in, out);\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 1u);
}

TEST(PlaPersonalityFormat, ArrayAndPlaneFormatsDifferOnSameMemory) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:1] in;\n"
      "  logic [1:1] mem [1:1];\n"
      "  logic [1:1] outa;\n"
      "  logic [1:1] outp;\n"
      "  initial begin\n"
      "    mem[1] = 1'b0;\n"
      "    in = 1'b1;\n"
      "    $sync$and$array(mem, in, outa);\n"
      "    $sync$and$plane(mem, in, outp);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* outa = f.ctx.FindVariable("outa");
  auto* outp = f.ctx.FindVariable("outp");
  ASSERT_NE(outa, nullptr);
  ASSERT_NE(outp, nullptr);
  EXPECT_EQ(outa->value.ToUint64(), 1u);
  EXPECT_EQ(outp->value.ToUint64(), 0u);
}

TEST(PlaPersonalityFormat, PlaneFormatWorstCaseCodeYieldsUnknown) {
  SimFixture f;
  auto* out = RunAndFindVar(
      "module t;\n"
      "  logic [1:1] in;\n"
      "  logic [1:1] mem [1:1];\n"
      "  logic [1:1] out;\n"
      "  initial begin\n"
      "    mem[1] = 1'bx;\n"
      "    in = 1'b1;\n"
      "    $sync$and$plane(mem, in, out);\n"
      "  end\n"
      "endmodule\n",
      f, "out");
  ASSERT_NE(out, nullptr);
  EXPECT_FALSE(out->value.IsKnown());
}

TEST(PlaPersonalityFormat, ArrayFormatUnknownCodeDoesNotTakeInput) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:2] in;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:1] outx;\n"
      "  logic [1:1] outz;\n"
      "  initial begin\n"
      "    in = 2'b01;\n"
      "    mem[1] = 2'bx1;\n"
      "    $sync$and$array(mem, in, outx);\n"
      "    mem[1] = 2'bz1;\n"
      "    $sync$and$array(mem, in, outz);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* outx = f.ctx.FindVariable("outx");
  auto* outz = f.ctx.FindVariable("outz");
  ASSERT_NE(outx, nullptr);
  ASSERT_NE(outz, nullptr);
  EXPECT_EQ(outx->value.ToUint64(), 1u);
  EXPECT_TRUE(outx->value.IsKnown());
  EXPECT_EQ(outz->value.ToUint64(), 1u);
  EXPECT_TRUE(outz->value.IsKnown());
}

TEST(PlaPersonalityFormat, PlaneFormatZIsDontCareAndQuestionMarkEqualsZ) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:2];\n"
                           "  logic [1:2] out;\n"
                           "  initial begin\n"
                           "    mem[1] = 2'b1z;\n"
                           "    mem[2] = 2'b1?;\n"
                           "    in = 2'b11;\n"
                           "    $sync$and$plane(mem, in, out);\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 0b11u);
}

TEST(PlaPersonalityFormat, ArrayFormatExampleOneLoadedFromReadmembFile) {
  SimFixture f;
  std::string path =
      WritePersonalityFile("example1", "1100000\n0011100\n0000111\n");
  std::string src =
      "module t;\n"
      "  logic a1, a2, a3, a4, a5, a6, a7;\n"
      "  logic b1, b2, b3;\n"
      "  logic [1:7] mem [1:3];\n"
      "  initial begin\n"
      "    a1 = 1; a2 = 1; a3 = 1; a4 = 0; a5 = 1; a6 = 1; a7 = 1;\n"
      "    $readmemb(\"" +
      path +
      "\", mem);\n"
      "    $async$and$array(mem, {a1,a2,a3,a4,a5,a6,a7}, {b1,b2,b3});\n"
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateSrc(src.c_str(), f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  std::remove(path.c_str());
  auto* b1 = f.ctx.FindVariable("b1");
  auto* b2 = f.ctx.FindVariable("b2");
  auto* b3 = f.ctx.FindVariable("b3");
  ASSERT_NE(b1, nullptr);
  ASSERT_NE(b2, nullptr);
  ASSERT_NE(b3, nullptr);
  EXPECT_EQ(b1->value.ToUint64(), 1u);
  EXPECT_EQ(b2->value.ToUint64(), 0u);
  EXPECT_EQ(b3->value.ToUint64(), 1u);
}

TEST(PlaPersonalityFormat, PlaneFormatCodesLoadedFromReadmembFile) {
  SimFixture f;
  std::string path = WritePersonalityFile("planecodes", "1z\n0z\n");
  std::string src =
      "module t;\n"
      "  logic [1:2] in;\n"
      "  logic [1:2] mem [1:2];\n"
      "  logic [1:2] out;\n"
      "  initial begin\n"
      "    in = 2'b11;\n"
      "    $readmemb(\"" +
      path +
      "\", mem);\n"
      "    $sync$and$plane(mem, in, out);\n"
      "  end\n"
      "endmodule\n";
  uint64_t out = RunModule(f, src.c_str(), "out");
  std::remove(path.c_str());
  EXPECT_EQ(out, 0b10u);
}

TEST(PlaPersonalityFormat, PlaneFormatMatchesLrmExample) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:3] a;\n"
      "  logic [1:3] mem [1:4];\n"
      "  logic [1:4] b;\n"
      "  logic [1:4] c111, c000, c101;\n"
      "  initial begin\n"
      "    mem[1] = 3'b10?;\n"
      "    mem[2] = 3'b??1;\n"
      "    mem[3] = 3'b0?0;\n"
      "    mem[4] = 3'b???;\n"
      "    a = 3'b111; $sync$and$plane(mem, a, b); c111 = b;\n"
      "    a = 3'b000; $sync$and$plane(mem, a, b); c000 = b;\n"
      "    a = 3'b101; $sync$and$plane(mem, a, b); c101 = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* c111 = f.ctx.FindVariable("c111");
  auto* c000 = f.ctx.FindVariable("c000");
  auto* c101 = f.ctx.FindVariable("c101");
  ASSERT_NE(c111, nullptr);
  ASSERT_NE(c000, nullptr);
  ASSERT_NE(c101, nullptr);
  EXPECT_EQ(c111->value.ToUint64(), 0b0101u);
  EXPECT_EQ(c000->value.ToUint64(), 0b0011u);
  EXPECT_EQ(c101->value.ToUint64(), 0b1101u);
}

TEST(PlaPersonalityFormat, AsyncPlaneExampleDisplaysEachResult) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module pla;\n"
                       "  logic [1:3] a, mem[1:4];\n"
                       "  logic [1:4] b;\n"
                       "  initial begin\n"
                       "    $async$and$plane(mem, a[1:3], b[1:4]);\n"
                       "    mem[1] = 3'b10?;\n"
                       "    mem[2] = 3'b??1;\n"
                       "    mem[3] = 3'b0?0;\n"
                       "    mem[4] = 3'b???;\n"
                       "    #10 a = 3'b111;\n"
                       "    #10 $displayb(a, \" -> \", b);\n"
                       "    #10 a = 3'b000;\n"
                       "    #10 $displayb(a, \" -> \", b);\n"
                       "    #10 a = 3'bxxx;\n"
                       "    #10 $displayb(a, \" -> \", b);\n"
                       "    #10 a = 3'b101;\n"
                       "    #10 $displayb(a, \" -> \", b);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "111 -> 0101\n000 -> 0011\nxxx -> xxx1\n101 -> 1101\n");
}

}  // namespace
