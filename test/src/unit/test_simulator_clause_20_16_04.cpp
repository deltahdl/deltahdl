#include <cstdio>
#include <fstream>
#include <string>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Writes `data` to a scratch file tagged by `tag` and returns its path. The
// path holds no characters that need escaping inside a SystemVerilog string
// literal, so it embeds directly in the source under test.
std::string WritePersonalityFile(const std::string& tag,
                                 const std::string& data) {
  std::string path = "/tmp/deltahdl_t201604_" + tag + ".mem";
  std::ofstream ofs(path);
  ofs << data;
  ofs.close();
  return path;
}

// §20.16.4 defines the two PLA personality formats that the simulator's PLA
// engine (eval_systask_pla.cpp) interprets when reducing a personality word.
// The array format reads each bit as a plain take/don't-take selector, while
// the plane format reads each bit as a Berkeley Espresso code that also chooses
// the polarity of the participating input. These tests drive small synchronous
// arrays so the per-bit interpretation is observable from the output term.

// §20.16.4 array format: "A 1 means take the input value, and a 0 means do not
// take the input value." With an AND-array selecting only the high input, the
// low input (whose personality bit is 0) is excluded from the reduction, so a
// low value there cannot pull the AND result down.
TEST(PlaPersonalityFormat, ArrayFormatOneTakesInputZeroExcludesIt) {
  SimFixture f;
  uint64_t out = RunModule(
      f,
      "module t;\n"
      "  logic [1:2] in;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:1] out;\n"
      "  initial begin\n"
      "    mem[1] = 2'b10;\n"  // take the high input, do not take the low one
      "    in = 2'b10;\n"      // high = 1, low = 0
      "    $sync$and$array(mem, in, out);\n"
      "  end\n"
      "endmodule\n",
      "out");
  EXPECT_EQ(out, 1u);
}

// §20.16.4: the two personality formats are differentiated by whether the array
// or the plane system call is used, and they interpret the very same memory bit
// differently. Driving identical personality memory and inputs through an
// AND-array and an AND-plane, a 0 bit means "do not take the input" in the
// array format (leaving the AND identity 1) but "take the complemented input"
// in the plane format (~1 = 0). The two calls therefore disagree on the same
// memory.
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
  EXPECT_EQ(outa->value.ToUint64(), 1u);  // array: 0 excludes the input
  EXPECT_EQ(outp->value.ToUint64(), 0u);  // plane: 0 complements the input
}

// §20.16.4 plane format: an x code takes the "worst case" of the input value.
// The engine contributes an unknown for that term, so the reduced output bit is
// itself unknown rather than a clean 0 or 1.
TEST(PlaPersonalityFormat, PlaneFormatWorstCaseCodeYieldsUnknown) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* out = f.ctx.FindVariable("out");
  ASSERT_NE(out, nullptr);
  EXPECT_FALSE(out->value.IsKnown());
}

// §20.16.4 array format, negative side: only a 1 takes the input value. A
// personality bit of x or z is not a 1, so — like a 0 — it must not take the
// input. The input under the unknown code is 0, which would force the AND
// result low were it taken (and an unknown contribution would make the result
// unknown), so a clean 1 on the output proves the code excluded the input.
TEST(PlaPersonalityFormat, ArrayFormatUnknownCodeDoesNotTakeInput) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:2] in;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:1] outx;\n"
      "  logic [1:1] outz;\n"
      "  initial begin\n"
      "    in = 2'b01;\n"      // high = 0 (under the x/z code), low = 1
      "    mem[1] = 2'bx1;\n"  // x code on the high input, 1 on the low
      "    $sync$and$array(mem, in, outx);\n"
      "    mem[1] = 2'bz1;\n"  // z code on the high input, 1 on the low
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

// §20.16.4 plane format: a z code means the input value is of no significance,
// and ? is the same as z. Two personality words identical except that one
// writes the don't-care as z and the other as ? must produce the same output
// bit. With the participating true input at 1 and the dropped input also at 1,
// a complement reading of the code would give 1 & ~1 = 0 and a worst-case
// reading would give x, so a known 1 in both positions pins the don't-care
// meaning and the z/? equivalence together.
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

// §20.16.4, Example 1: the array-format personality is loaded from a text data
// file with §21.4's $readmemb (the loading form §20.16.3 provides), the input
// and output terms are concatenations of scalar signals, and each personality
// word implements one logic equation:
//   b1 = a1 & a2;  b2 = a3 & a4 & a5;  b3 = a5 & a6 & a7;
// With a4 = 0 and every other input 1, only b2's word selects a4, so b2 falls
// to 0 while b1 and b3 stay 1 — the 0 columns of each word exclude their
// inputs and the 1 columns take them, per word, end to end from the file.
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
  std::remove(path.c_str());
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
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

// §20.16.4 plane format, file-loaded input form: the Espresso codes can also
// arrive in the personality memory through §21.4's $readmemb, whose binary
// words admit the 4-state digits the plane decode assigns meanings to. A file
// word "1z" keeps only the true high input (1) while "0z" keeps only its
// complement (0), so with both inputs at 1 the two output terms disagree —
// observable only if the file-loaded codes reach the same per-bit decode as
// procedurally assigned ones.
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

// §20.16.4, Example 2: the $async$and$plane example. The personality encodes
//   b[1] = a[1] & ~a[2];  b[2] = a[3];  b[3] = ~a[1] & ~a[3];  b[4] = 1;
// via the plane codes in mem[1..4]. Applying the known input vectors from the
// example's printed output must reproduce that output exactly, exercising the
// 0/1/don't-care codes together. (b is logic [1:4], MSB = b[1].)
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
  EXPECT_EQ(c111->value.ToUint64(), 0b0101u);  // 111 -> 0101
  EXPECT_EQ(c000->value.ToUint64(), 0b0011u);  // 000 -> 0011
  EXPECT_EQ(c101->value.ToUint64(), 0b1101u);  // 101 -> 1101
}

}  // namespace
