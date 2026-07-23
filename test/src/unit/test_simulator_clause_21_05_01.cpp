// §21.5.1 Writing packed data — $writememb / $writememh treat packed data
// exactly as $readmemb / $readmemh do (see §21.4.1): each element of an
// unpacked array is handled as its vector equivalent, so every element is
// written as ONE number of the element's full packed width — never split per
// packed sub-dimension or per structure member — in the radix the companion
// read task parses.
//
// The rule is a runtime rule whose behavior depends on how the memory operand
// is produced: the element's packed shape (§7.4 vector, packed structure,
// multidimensional packed) and the container declaring it (fixed unpacked
// array, queue — §21.4.1's forms). These tests therefore declare each source
// memory with real syntax and drive the module through the full pipeline
// (parse -> elaborate -> lower -> run), observing the dumped file text and the
// round trip through the matching read task — the two faces of "identical
// treatment" — rather than hand-building array state on a bare context.
#include <cstdio>
#include <fstream>
#include <iostream>
#include <iterator>
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

// Reads back the whole contents of a file a run dumped with $writemem.
std::string SlurpFile(const std::string& path) {
  std::ifstream ifs(path);
  return std::string((std::istreambuf_iterator<char>(ifs)),
                     std::istreambuf_iterator<char>());
}

// §21.5.1: a packed-vector element wider than one file digit is written as one
// whole multi-digit number per line — the same whole-word treatment §21.4.1
// gives the load side — and reloads through $readmemh unchanged.
TEST(WritememPackedDataSim, PackedVectorElementWrittenAsWholeWord) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210501_vec.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [15:0] src [0:1];\n"
      "  logic [15:0] dst [0:1];\n"
      "  initial begin\n"
      "    src[0] = 16'hABCD; src[1] = 16'h1234;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%h %h\", dst[0], dst[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "abcd 1234\n");
  EXPECT_EQ(SlurpFile(path), "abcd\n1234\n");
  std::remove(path.c_str());
}

// §21.5.1: an element of a packed structure type is written as the vector
// equivalent of the structure — one number covering all members, not one
// number per member — mirroring the read side's §21.4.1 treatment, and the
// dump reloads into an array of the same structure type intact.
TEST(WritememPackedDataSim, PackedStructElementWrittenAsVectorEquivalent) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210501_pstruct.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct packed { logic [3:0] hi; logic [11:0] lo; } st_t;\n"
      "  st_t src [0:1];\n"
      "  st_t dst [0:1];\n"
      "  initial begin\n"
      "    src[0] = 16'hABCD; src[1] = 16'h1234;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%h %h\", dst[0], dst[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "abcd 1234\n");
  EXPECT_EQ(SlurpFile(path), "abcd\n1234\n");
  std::remove(path.c_str());
}

// §21.5.1: a multidimensional packed element ([1:0][7:0]) is one flat vector,
// so the dump writes one flat number per element rather than one number per
// packed subword — the mirror of §21.4.1's flat-vector load.
TEST(WritememPackedDataSim, MultiDimPackedElementWrittenAsFlatVector) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210501_mdp.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [1:0][7:0] src [0:1];\n"
      "  logic [1:0][7:0] dst [0:1];\n"
      "  initial begin\n"
      "    src[0] = 16'hBEEF; src[1] = 16'hCAFE;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%h %h\", dst[0], dst[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "beef cafe\n");
  EXPECT_EQ(SlurpFile(path), "beef\ncafe\n");
  std::remove(path.c_str());
}

// §21.5.1: a packed element wider than 64 bits is still one word; every
// machine word of the multi-word value lands in the single dumped number, and
// the reload reproduces the high words intact.
TEST(WritememPackedDataSim, WidePackedElementWrittenWhole) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210501_wide.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [79:0] src [0:0];\n"
      "  logic [79:0] dst [0:0];\n"
      "  initial begin\n"
      "    src[0] = 80'h0123456789ABCDEF0123;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%h\", dst[0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "0123456789abcdef0123\n");
  EXPECT_EQ(SlurpFile(path), "0123456789abcdef0123\n");
  std::remove(path.c_str());
}

// §21.5.1: the packed range's bounds do not change the vector-equivalent
// treatment — a nonzero-lsb element ([11:4]) and an ascending-range element
// ([0:15]) are each written at the element's declared width and round-trip
// through the matching read task.
TEST(WritememPackedDataSim, PackedRangeVariantsWrittenAtDeclaredWidth) {
  SimFixture f;
  std::string path_r = "/tmp/deltahdl_t210501_rng.mem";
  std::string path_a = "/tmp/deltahdl_t210501_asc.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [11:4] rsrc [0:1];\n"
      "  logic [11:4] rdst [0:1];\n"
      "  logic [0:15] asrc [0:1];\n"
      "  logic [0:15] adst [0:1];\n"
      "  initial begin\n"
      "    rsrc[0] = 8'hA5; rsrc[1] = 8'h5A;\n"
      "    $writememh(\"" +
          path_r +
          "\", rsrc);\n"
          "    $readmemh(\"" +
          path_r +
          "\", rdst);\n"
          "    asrc[0] = 16'hF00D; asrc[1] = 16'h0DDC;\n"
          "    $writememh(\"" +
          path_a +
          "\", asrc);\n"
          "    $readmemh(\"" +
          path_a +
          "\", adst);\n"
          "    $display(\"%h %h %h %h\", rdst[0], rdst[1], adst[0], adst[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "a5 5a f00d 0ddc\n");
  EXPECT_EQ(SlurpFile(path_r), "a5\n5a\n");
  EXPECT_EQ(SlurpFile(path_a), "f00d\n0ddc\n");
  std::remove(path_r.c_str());
  std::remove(path_a.c_str());
}

// §21.5.1: packed data is four-state, and $writememb writes it exactly as
// $readmemb reads it — one digit per bit, with x and z bits emitted as
// distinct digits in their bit positions rather than collapsed to a known
// number. The reload reproduces the unknown and high-impedance bits.
TEST(WritememPackedDataSim, WritemembEmitsPerBitFourStateDigits) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210501_b4.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] src [0:0];\n"
      "  logic [7:0] dst [0:0];\n"
      "  initial begin\n"
      "    src[0] = 8'b10xz1001;\n"
      "    $writememb(\"" +
          path +
          "\", src);\n"
          "    $readmemb(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%b\", dst[0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "10xz1001\n");
  EXPECT_EQ(SlurpFile(path), "10xz1001\n");
  std::remove(path.c_str());
}

// §21.5.1: a hex digit whose four bits are all-x or all-z is within the read
// task's digit vocabulary, so $writememh emits the x / z digit itself and the
// $readmemh reload reproduces those digit groups exactly.
TEST(WritememPackedDataSim, WritememhEmitsWholeDigitUnknownAndHighZ) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210501_h4.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [15:0] src [0:0];\n"
      "  logic [15:0] dst [0:0];\n"
      "  initial begin\n"
      "    src[0] = 16'hax_z5;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%h\", dst[0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "axz5\n");
  EXPECT_EQ(SlurpFile(path), "axz5\n");
  std::remove(path.c_str());
}

// §21.5.1 negative boundary: a hex digit position with PARTIALLY unknown bits
// has no exact digit in the read task's vocabulary. Identical treatment means
// the writer must still emit something $readmemh parses — the capital-X
// mixed-unknown digit — not a form the reload would choke on; the round trip
// degrades that nibble to all-x while the fully known nibble survives.
TEST(WritememPackedDataSim, MixedUnknownNibbleDegradesToReadableDigit) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210501_mix.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] src [0:0];\n"
      "  logic [7:0] dst [0:0];\n"
      "  initial begin\n"
      "    src[0] = 8'b1x0z0101;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%b\", dst[0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "xxxx0101\n");
  EXPECT_EQ(SlurpFile(path), "X5\n");
  std::remove(path.c_str());
}

// §21.5.1: the vector-equivalent treatment is container-independent — a queue
// of packed vectors (§21.4.1's container, populated by push_back) dumps one
// whole word per element in the same form a fixed array does, and the file
// reloads through $readmemh.
TEST(WritememPackedDataSim, QueueOfPackedElementsWrittenAsWholeWords) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210501_queue.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [15:0] q [$];\n"
      "  logic [15:0] dst [0:1];\n"
      "  initial begin\n"
      "    q.push_back(16'hABCD); q.push_back(16'h1234);\n"
      "    $writememh(\"" +
          path +
          "\", q);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%h %h\", dst[0], dst[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "abcd 1234\n");
  EXPECT_EQ(SlurpFile(path), "abcd\n1234\n");
  std::remove(path.c_str());
}

}  // namespace
