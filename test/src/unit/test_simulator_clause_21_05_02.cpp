// §21.5.2 Writing 2-state types — $writememb / $writememh can dump unpacked
// arrays whose element type is a 2-state type (such as int) or an enumerated
// type. For an enumerated element type, the value placed in the file is the
// enum member's ordinal value — its underlying integer value per §6.19 — never
// the member's name or its declaration position.
//
// Both rules are runtime rules whose behavior depends on how the memory
// operand is produced: the element's 2-state type (int / byte / shortint /
// longint / bit vector), the §6.19 enum declaration supplying the ordinal
// values, and the container declaring the array (fixed unpacked array, queue,
// dynamic array). These tests therefore declare each source memory with real
// syntax and drive the module through the full pipeline (parse -> elaborate ->
// lower -> run), observing the dumped file text and the round trip through the
// matching read task, rather than hand-building array state on a bare context.
//
// Not exercised here: an anonymous (inline) enum declaration — its member
// constants evaluate to 0 even in a plain $display, an upstream §6.19 defect
// that never reaches the write task. Typedef'd enums carry their ordinals
// correctly and are the forms used below.
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

// §21.5.2: an unpacked array of int — the subclause's own example type — is
// dumped one word per line as a plain number at the type's full 32-bit width.
// A negative value and a value with the sign bit set are just their two's-
// complement bit patterns, and the dump reloads through $readmemh unchanged.
TEST(WritememTwoStateSim, IntArrayWrittenAsPlainNumbers) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210502_int.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  int src [0:2];\n"
      "  int dst [0:2];\n"
      "  initial begin\n"
      "    src[0] = 42; src[1] = -1; src[2] = 32'hDEADBEEF;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%h %h %h\", dst[0], dst[1], dst[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "0000002a ffffffff deadbeef\n");
  EXPECT_EQ(SlurpFile(path), "0000002a\nffffffff\ndeadbeef\n");
  std::remove(path.c_str());
}

// §21.5.2: the rule admits every 2-state integer atom type, and each is
// written at its own type width — byte as two hex digits, shortint as four,
// longint as sixteen (with every machine word of the 64-bit value present).
TEST(WritememTwoStateSim, NarrowAndWideIntegerTypesWrittenAtTypeWidth) {
  SimFixture f;
  std::string path_b = "/tmp/deltahdl_t210502_byte.mem";
  std::string path_s = "/tmp/deltahdl_t210502_short.mem";
  std::string path_l = "/tmp/deltahdl_t210502_long.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  byte bsrc [0:1];\n"
      "  shortint ssrc [0:1];\n"
      "  longint lsrc [0:1];\n"
      "  longint ldst [0:1];\n"
      "  initial begin\n"
      "    bsrc[0] = 8'h2A; bsrc[1] = 8'hF0;\n"
      "    $writememh(\"" +
          path_b +
          "\", bsrc);\n"
          "    ssrc[0] = 16'hBEEF; ssrc[1] = 16'h0001;\n"
          "    $writememh(\"" +
          path_s +
          "\", ssrc);\n"
          "    lsrc[0] = 64'hFEDCBA9876543210; lsrc[1] = 64'h1;\n"
          "    $writememh(\"" +
          path_l +
          "\", lsrc);\n"
          "    $readmemh(\"" +
          path_l +
          "\", ldst);\n"
          "    $display(\"%h %h\", ldst[0], ldst[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "fedcba9876543210 0000000000000001\n");
  EXPECT_EQ(SlurpFile(path_b), "2a\nf0\n");
  EXPECT_EQ(SlurpFile(path_s), "beef\n0001\n");
  EXPECT_EQ(SlurpFile(path_l), "fedcba9876543210\n0000000000000001\n");
  std::remove(path_b.c_str());
  std::remove(path_s.c_str());
  std::remove(path_l.c_str());
}

// §21.5.2: a bit-vector element type is 2-state too, and the binary task
// writes it one 0/1 digit per bit — the form $readmemb loads back intact.
TEST(WritememTwoStateSim, BitVectorArrayWrittenPerBitByWritememb) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210502_bits.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] src [0:1];\n"
      "  bit [7:0] dst [0:1];\n"
      "  initial begin\n"
      "    src[0] = 8'b10100101; src[1] = 8'b00001111;\n"
      "    $writememb(\"" +
          path +
          "\", src);\n"
          "    $readmemb(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%b %b\", dst[0], dst[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "10100101 00001111\n");
  EXPECT_EQ(SlurpFile(path), "10100101\n00001111\n");
  std::remove(path.c_str());
}

// §21.5.2 negative boundary: a 2-state word cannot hold an unknown or
// high-impedance bit, so no x or z token can ever appear in the dump — the
// nearest would-be-rejected input. A default-initialized int array (which a
// 4-state type would dump as x words) writes plain zero words in both radices.
TEST(WritememTwoStateSim, DefaultTwoStateArrayWritesZerosNeverFourStateDigits) {
  SimFixture f;
  std::string path_h = "/tmp/deltahdl_t210502_zh.mem";
  std::string path_b = "/tmp/deltahdl_t210502_zb.mem";
  RunCapture(
      "module t;\n"
      "  int zmem [0:1];\n"
      "  initial begin\n"
      "    $writememh(\"" +
          path_h +
          "\", zmem);\n"
          "    $writememb(\"" +
          path_b +
          "\", zmem);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path_h), "00000000\n00000000\n");
  EXPECT_EQ(SlurpFile(path_b),
            "00000000000000000000000000000000\n"
            "00000000000000000000000000000000\n");
  std::remove(path_h.c_str());
  std::remove(path_b.c_str());
}

// §21.5.2: a 2-state element wider than one machine word (bit [71:0]) is still
// one number per line; the high machine word survives the dump and the reload.
TEST(WritememTwoStateSim, WideTwoStateElementWrittenWhole) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210502_wide.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  bit [71:0] src [0:0];\n"
      "  bit [71:0] dst [0:0];\n"
      "  initial begin\n"
      "    src[0] = 72'hAB_CDEF0123_456789AB;\n"
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
  EXPECT_EQ(out, "abcdef0123456789ab\n");
  EXPECT_EQ(SlurpFile(path), "abcdef0123456789ab\n");
  std::remove(path.c_str());
}

// §21.5.2: the 2-state admission is container-independent — a queue of int
// (populated by push_back) and a dynamic array of int (sized by new[]) each
// dump one plain word per line exactly like a fixed array, and each file
// reloads through $readmemh.
TEST(WritememTwoStateSim, TwoStateQueueAndDynamicArrayWritten) {
  SimFixture f;
  std::string path_q = "/tmp/deltahdl_t210502_q.mem";
  std::string path_d = "/tmp/deltahdl_t210502_d.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  int q [$];\n"
      "  int d [];\n"
      "  int dst [0:1];\n"
      "  initial begin\n"
      "    q.push_back(7); q.push_back(8);\n"
      "    $writememh(\"" +
          path_q +
          "\", q);\n"
          "    d = new[2]; d[0] = 3; d[1] = 4;\n"
          "    $writememh(\"" +
          path_d +
          "\", d);\n"
          "    $readmemh(\"" +
          path_q +
          "\", dst);\n"
          "    $display(\"%0d %0d\", dst[0], dst[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "7 8\n");
  EXPECT_EQ(SlurpFile(path_q), "00000007\n00000008\n");
  EXPECT_EQ(SlurpFile(path_d), "00000003\n00000004\n");
  std::remove(path_q.c_str());
  std::remove(path_d.c_str());
}

// §21.5.2: for an enumerated element type, the file holds each element's
// ordinal value per §6.19. The members carry explicit values 2 / 5 / 9 —
// deliberately not their 0 / 1 / 2 declaration positions — so the dump proves
// the value written is the member's underlying integer, not its position and
// not its name, and the file reloads into an array of the same enum type.
TEST(WritememTwoStateSim, EnumArrayWritesOrdinalValues) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210502_enum.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum int {RED=2, GREEN=5, BLUE=9} color_e;\n"
      "  color_e src [0:2];\n"
      "  color_e dst [0:2];\n"
      "  initial begin\n"
      "    src[0] = GREEN; src[1] = RED; src[2] = BLUE;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%0d %0d %0d\", dst[0], dst[1], dst[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "5 2 9\n");
  // Ordinal values 5, 2, 9 at the int base width — no member names, no
  // declaration positions.
  EXPECT_EQ(SlurpFile(path), "00000005\n00000002\n00000009\n");
  std::remove(path.c_str());
}

// §21.5.2: when the §6.19 declaration gives no explicit values, the members'
// ordinals are the auto-assigned 0, 1, 2, ... — the elements are stored in
// reverse member order here, so the file order (2, 0, 1) tracks the element
// values, not the element indices.
TEST(WritememTwoStateSim, EnumAutoOrdinalsFollowDeclarationOrder) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210502_auto.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum {ALPHA, BETA, GAMMA} abc_e;\n"
      "  abc_e src [0:2];\n"
      "  abc_e dst [0:2];\n"
      "  initial begin\n"
      "    src[0] = GAMMA; src[1] = ALPHA; src[2] = BETA;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%0d %0d %0d\", dst[0], dst[1], dst[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "2 0 1\n");
  EXPECT_EQ(SlurpFile(path), "00000002\n00000000\n00000001\n");
  std::remove(path.c_str());
}

// §21.5.2: the ordinal-value rule holds for the binary task too — $writememb
// writes each enum element's ordinal as its full-width bit pattern, and the
// dump reloads through $readmemb into an array of the same enum type.
TEST(WritememTwoStateSim, EnumArrayWritemembWritesOrdinalBits) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210502_enumb.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum int {RED=2, GREEN=5, BLUE=9} color_e;\n"
      "  color_e src [0:2];\n"
      "  color_e dst [0:2];\n"
      "  initial begin\n"
      "    src[0] = GREEN; src[1] = RED; src[2] = BLUE;\n"
      "    $writememb(\"" +
          path +
          "\", src);\n"
          "    $readmemb(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%0d %0d %0d\", dst[0], dst[1], dst[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "5 2 9\n");
  EXPECT_EQ(SlurpFile(path),
            "00000000000000000000000000000101\n"
            "00000000000000000000000000000010\n"
            "00000000000000000000000000001001\n");
  std::remove(path.c_str());
}

}  // namespace
