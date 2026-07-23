#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §21.3.4.4 governs $fread, which loads raw bytes from a file descriptor into
// either an integral variable (the variant applied for all packed data) or a
// memory. Loading is byte-by-byte and big endian within each element; a
// memory load starts at the optional start address (else the lowest declared
// address) and walks toward the highest address, capped by the optional
// count; loaded bits are always 2-value; the call returns the number of
// bytes read, or zero on error, with $ferror describing a failure. Every
// rule operates on a §21.3.1 descriptor and on a destination produced by a
// declaration, so each test builds both from real source syntax and drives
// the full pipeline.

// Runs a single-module source through parse -> elaborate -> lower -> run while
// capturing everything the run writes to stdout.
static std::string RunCapture(const std::string& src, SysTaskFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// Creates `path` holding the raw `bytes` so a read-type $fopen has binary
// data to deliver.
static void SeedBytes(const std::string& path,
                      const std::vector<uint8_t>& bytes) {
  std::ofstream ofs(path, std::ios::binary);
  ofs.write(reinterpret_cast<const char*>(bytes.data()),
            static_cast<std::streamsize>(bytes.size()));
}

// C1/C2/C8: the integral-variable variant loads the whole packed value at
// once, big endian -- the first byte read fills the most significant byte
// position. The return value is the number of bytes read.
TEST(FreadBinary, IntegralVariantReadsBigEndian) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_int_be.bin";
  SeedBytes(tmp, {0xDE, 0xAD, 0xBE, 0xEF});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  reg [31:0] v;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(v, fd);\n"
          "    $display(\"code=%0d v=%h\", code, v);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=4 v=deadbeef"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C2: a packed struct is packed data, so it is loaded through the integral
// variant as one whole value rather than member by member.
TEST(FreadBinary, PackedStructReadsAsWholeValue) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_packed.bin";
  SeedBytes(tmp, {0xAB, 0xCD});
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct packed { bit [7:0] hi; bit [7:0] lo; } pst_t;\n"
      "  integer fd, code;\n"
      "  pst_t p;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(p, fd);\n"
          "    $display(\"code=%0d p=%h\", code, p);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=2 p=abcd"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C2/C8: a packed destination wider than 64 bits still loads every byte, the
// first byte read occupying the most significant byte position.
TEST(FreadBinary, WidePackedValueLoadsAllBytes) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_wide.bin";
  SeedBytes(tmp, {0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A,
                  0x0B, 0x0C});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  logic [95:0] wide;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(wide, fd);\n"
          "    $display(\"code=%0d wide=%h\", code, wide);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=12 wide=0102030405060708090a0b0c"),
            std::string::npos)
      << out;
  std::remove(tmp.c_str());
}

// C2: the integral variant is the one applied for all packed data -- an
// integer destination (the standard's own example) loads big endian, and a
// multi-dimensional packed array loads as one whole value whose remaining
// byte fills the most significant element position.
TEST(FreadBinary, IntegerAndMultidimPackedArrayUseIntegralVariant) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_intpa.bin";
  SeedBytes(tmp, {0xCA, 0xFE, 0xBA, 0xBE, 0x7B});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code, iv;\n"
      "  logic [1:0][7:0] pa;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(iv, fd);\n"
          "    $display(\"code=%0d iv=%h\", code, iv);\n"
          "    code = $fread(pa, fd);\n"
          "    $display(\"code=%0d hi=%h lo=%h\", code, pa[1], pa[0]);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=4 iv=cafebabe"), std::string::npos) << out;
  EXPECT_NE(out.find("code=1 hi=7b lo=00"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C8/C12: when the file ends before the packed value is full, the bytes that
// were read keep their big-endian (most significant first) positions and the
// call returns how many bytes it actually got.
TEST(FreadBinary, PartialWordKeepsMostSignificantAlignment) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_partial.bin";
  SeedBytes(tmp, {0xEE});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  reg [15:0] v;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(v, fd);\n"
          "    $display(\"code=%0d v=%h\", code, v);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=1 v=ee00"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C5: start and count are ignored when the destination is an integral
// variable -- the value loads exactly as it would without them.
TEST(FreadBinary, StartCountIgnoredForIntegralVariable) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_ignore.bin";
  SeedBytes(tmp, {0x12, 0x34});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  reg [15:0] v;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(v, fd, 99, 1);\n"
          "    $display(\"code=%0d v=%h\", code, v);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=2 v=1234"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C3/C6: with no start argument, loading begins at the lowest declared
// address and fills consecutive words toward the highest.
TEST(FreadBinary, MemoryFillsConsecutiveWordsFromLowest) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_consec.bin";
  SeedBytes(tmp, {0x01, 0x02, 0x03, 0x04});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  bit [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(mem, fd);\n"
          "    $display(\"code=%0d m=%h %h %h %h\", code, mem[0], mem[1],\n"
          "             mem[2], mem[3]);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=4 m=01 02 03 04"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C3/C7: start is the address of the first element loaded. This is the
// standard's own example -- start=12 with memory up[10:20] puts the first
// word at up[12]; lower locations stay untouched. start arrives as a
// parameter and count as a localparam to cover the constant operand forms.
TEST(FreadBinary, StartAddressSelectsFirstElement) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_start.bin";
  SeedBytes(tmp, {0x11, 0x22});
  std::string out = RunCapture(
      "module t;\n"
      "  parameter S = 12;\n"
      "  localparam C = 2;\n"
      "  integer fd, code;\n"
      "  bit [7:0] up [10:20];\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(up, fd, S, C);\n"
          "    $display(\"code=%0d u10=%h u12=%h u13=%h u14=%h\", code,\n"
          "             up[10], up[12], up[13], up[14]);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=2 u10=00 u12=11 u13=22 u14=00"), std::string::npos)
      << out;
  std::remove(tmp.c_str());
}

// C7: the standard's descending example -- for memory down[20:10] with
// start=12, the first location loaded is down[12], then down[13]: addresses
// ascend numerically regardless of the declared range direction.
TEST(FreadBinary, DescendingMemoryLoadsAscendingAddresses) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_down.bin";
  SeedBytes(tmp, {0x33, 0x44});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  bit [7:0] down [20:10];\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(down, fd, 12);\n"
          "    $display(\"code=%0d d12=%h d13=%h d20=%h\", code, down[12],\n"
          "             down[13], down[20]);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=2 d12=33 d13=44 d20=00"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C4: count caps how many locations are loaded even when more data and more
// memory are available; start and count here are plain variables.
TEST(FreadBinary, CountLimitsWordsLoaded) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_count.bin";
  SeedBytes(tmp, {0xA1, 0xA2, 0xA3, 0xA4});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code, sv, cv;\n"
      "  bit [7:0] mem [0:7];\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    sv = 2; cv = 2;\n"
          "    code = $fread(mem, fd, sv, cv);\n"
          "    $display(\"code=%0d m2=%h m3=%h m4=%h\", code, mem[2], mem[3],\n"
          "             mem[4]);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=2 m2=a1 m3=a2 m4=00"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C3/C4: the $fread(mem, fd, , count) call form from the standard's example
// list -- start is omitted, so loading begins at the lowest address while
// count still caps the locations loaded.
TEST(FreadBinary, OmittedStartFormDefaultsToLowestAddress) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_nostart.bin";
  SeedBytes(tmp, {0x11, 0x22, 0x33, 0x44});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  bit [7:0] mem [0:7];\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(mem, fd, , 3);\n"
          "    $display(\"code=%0d m0=%h m1=%h m2=%h m3=%h\", code, mem[0],\n"
          "             mem[1], mem[2], mem[3]);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=3 m0=11 m1=22 m2=33 m3=00"), std::string::npos)
      << out;
  std::remove(tmp.c_str());
}

// C4/C6: without a count, the memory is filled with whatever data are
// available -- a short file loads only its own bytes and the return value
// reports that shorter count.
TEST(FreadBinary, NoCountFillsWithAvailableData) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_short.bin";
  SeedBytes(tmp, {0x77, 0x88});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  bit [7:0] mem [0:7];\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(mem, fd);\n"
          "    $display(\"code=%0d m0=%h m1=%h m2=%h\", code, mem[0], mem[1],\n"
          "             mem[2]);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=2 m0=77 m1=88 m2=00"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C8: a 9-bit-wide memory consumes two bytes per word, big endian; bits above
// the element width are truncated away (0x02AA keeps only its low 9 bits).
TEST(FreadBinary, NineBitWordsUseTwoBytesAndTruncate) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_nine.bin";
  SeedBytes(tmp, {0x01, 0x99, 0x02, 0xAA});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  bit [8:0] mem [0:1];\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(mem, fd);\n"
          "    $display(\"code=%0d m0=%h m1=%h\", code, mem[0], mem[1]);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=4 m0=199 m1=0aa"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C8: memory elements wider than 64 bits consume their full byte quota per
// word, each word big endian.
TEST(FreadBinary, WideMemoryWordsLoadAllBytes) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_widemem.bin";
  SeedBytes(tmp, {0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                  0x09, 0x0A, 0x0B, 0x0C, 0xA1, 0xA2, 0xA3, 0xA4,
                  0xA5, 0xA6, 0xA7, 0xA8, 0xA9, 0xAA, 0xAB, 0xAC});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  bit [95:0] mem [0:1];\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(mem, fd);\n"
          "    $display(\"code=%0d m0=%h m1=%h\", code, mem[0], mem[1]);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(
      out.find(
          "code=24 m0=0102030405060708090a0b0c m1=a1a2a3a4a5a6a7a8a9aaabac"),
      std::string::npos)
      << out;
  std::remove(tmp.c_str());
}

// C9: an unpacked struct is read as though a separate $fread were performed
// on each member in declaration order -- each member takes its own whole
// number of bytes.
TEST(FreadBinary, UnpackedStructReadsMembersInDeclarationOrder) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_ustruct.bin";
  SeedBytes(tmp, {0xAA, 0xBB, 0xCC});
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct { bit [7:0] a; bit [15:0] b; } st_t;\n"
      "  integer fd, code;\n"
      "  st_t s;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(s, fd);\n"
          "    $display(\"code=%0d a=%h b=%h\", code, s.a, s.b);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=3 a=aa b=bbcc"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C9/C8: a member wider than 64 bits loads intact within an unpacked struct,
// and the following member continues from the next file byte.
TEST(FreadBinary, UnpackedStructWideMemberLoadsIntact) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_wstruct.bin";
  SeedBytes(tmp, {0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A,
                  0x0B, 0x0C, 0xA1});
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct { bit [95:0] w; bit [7:0] tl; } ws_t;\n"
      "  integer fd, code;\n"
      "  ws_t s;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(s, fd);\n"
          "    $display(\"code=%0d w=%h tl=%h\", code, s.w, s.tl);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=13 w=0102030405060708090a0b0c tl=a1"),
            std::string::npos)
      << out;
  std::remove(tmp.c_str());
}

// C10: an unpacked union is read as though the operation were performed on
// the first member in declaration order only -- one byte here, not two.
TEST(FreadBinary, UnpackedUnionReadsFirstMemberOnly) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_union.bin";
  SeedBytes(tmp, {0xDD, 0x5E});
  std::string out = RunCapture(
      "module t;\n"
      "  typedef union { bit [7:0] a; bit [15:0] b; } un_t;\n"
      "  integer fd, code;\n"
      "  un_t u;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(u, fd);\n"
          "    $display(\"code=%0d a=%h\", code, u.a);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=1 a=dd"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C11: the loaded data are 2-value -- a 4-state variable holding x before the
// read holds a fully known value afterward; x or z can never be read in.
TEST(FreadBinary, LoadedDataIsTwoValue) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_twoval.bin";
  SeedBytes(tmp, {0x5A});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  logic [7:0] lx;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    $display(\"pre=%h\", lx);\n"
          "    code = $fread(lx, fd);\n"
          "    $display(\"code=%0d post=%h\", code, lx);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("pre=xx"), std::string::npos) << out;
  EXPECT_NE(out.find("code=1 post=5a"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C6: loading stops when the file is exhausted -- a location beyond the data
// keeps whatever value it held before the call.
TEST(FreadBinary, UnreadMemoryLocationKeepsPriorValue) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_partmem.bin";
  SeedBytes(tmp, {0x42});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  logic [7:0] mem [0:1];\n"
      "  initial begin\n"
      "    mem[1] = 8'h77;\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(mem, fd);\n"
          "    $display(\"code=%0d m0=%h m1=%h\", code, mem[0], mem[1]);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=1 m0=42 m1=77"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C12 negative: reading through a descriptor opened for writing is an error
// -- the call returns zero and $ferror reports a nonzero cause (§21.3.7).
TEST(FreadBinary, ErrorReturnsZeroAndFerrorReports) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_wmode.bin";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code, err;\n"
      "  bit [7:0] mem [0:1];\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    code = $fread(mem, fd);\n"
          "    err = $ferror(fd);\n"
          "    $display(\"code=%0d errnz=%0d\", code, err != 0);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=0 errnz=1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C12: exhausting the file is not an error -- a read at end-of-file simply
// returns zero bytes and $ferror stays clear.
TEST(FreadBinary, EndOfFileReturnsZeroWithoutError) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_eof.bin";
  SeedBytes(tmp, {0x10});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c1, c2, err;\n"
      "  bit [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    c1 = $fread(mem, fd);\n"
          "    c2 = $fread(mem, fd);\n"
          "    err = $ferror(fd);\n"
          "    $display(\"c1=%0d c2=%0d err=%0d\", c1, c2, err);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=1 c2=0 err=0"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C2/C8/C12: a 2-state int destination also goes through the integral
// variant -- a file shorter than the value still lands big endian, most
// significant bytes first, and the count reports the shortfall.
TEST(FreadBinary, TwoStateIntDestReadsBigEndian) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_int2s.bin";
  SeedBytes(tmp, {0x0F, 0xF0});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  int v;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(v, fd);\n"
          "    $display(\"code=%0d v=%h\", code, v);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=2 v=0ff00000"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C12 negative: a descriptor that has been closed refuses the read -- the
// call returns zero and $ferror reports a nonzero cause.
TEST(FreadBinary, ClosedDescriptorReturnsZeroAndFerrorReports) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_closed.bin";
  SeedBytes(tmp, {0x55});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code, err;\n"
      "  bit [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    $fclose(fd);\n"
          "    code = $fread(mem, fd);\n"
          "    err = $ferror(fd);\n"
          "    $display(\"code=%0d errnz=%0d\", code, err != 0);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=0 errnz=1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C3/C4/C6 over a §21.4-loaded memory: $readmemh seeds every location, then
// a windowed $fread(mem, fd, start, count) overwrites only the window --
// locations on either side keep the values the memory file gave them.
TEST(FreadBinary, WindowedLoadOverReadmemSeededMemory) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_window.bin";
  std::string mempath = "/tmp/deltahdl_213404_window.mem";
  SeedBytes(tmp, {0x0F, 0xF0});
  {
    std::ofstream ofs(mempath);
    ofs << "11\n22\n33\n44\n";
  }
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  bit [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          mempath +
          "\", mem);\n"
          "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    code = $fread(mem, fd, 1, 2);\n"
          "    $display(\"code=%0d m=%h %h %h %h\", code, mem[0], mem[1],\n"
          "             mem[2], mem[3]);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=2 m=11 0f f0 44"), std::string::npos) << out;
  std::remove(tmp.c_str());
  std::remove(mempath.c_str());
}

// C12 input form: $fread is a function, so its return value can sit directly
// inside a larger expression such as an if condition.
TEST(FreadBinary, ReturnValueUsableAsExpressionOperand) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213404_expr.bin";
  SeedBytes(tmp, {0x01, 0x02, 0x03, 0x04});
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd;\n"
      "  bit [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    if ($fread(mem, fd) == 4) $display(\"expr ok m3=%h\", mem[3]);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("expr ok m3=04"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

}  // namespace
