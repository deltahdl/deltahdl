#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §20.16.4 defines the two PLA personality formats that the simulator's PLA
// engine (eval_systask.cpp) interprets when reducing a personality word. The
// array format reads each bit as a plain take/don't-take selector, while the
// plane format reads each bit as a Berkeley Espresso code that also chooses the
// polarity of the participating input. These tests drive small synchronous
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

// §20.16.4 plane format: a 0 takes the complemented input value. This is the
// behavior that distinguishes the plane format from the array format - in the
// array format a 0 would simply drop the input, leaving the AND identity (1),
// whereas here the complemented true input (~1 = 0) drives the output low.
TEST(PlaPersonalityFormat, PlaneFormatZeroTakesComplementedInput) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:1] in;\n"
                           "  logic [1:1] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  initial begin\n"
                           "    mem[1] = 1'b0;\n"
                           "    in = 1'b1;\n"
                           "    $sync$and$plane(mem, in, out);\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 0u);
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
