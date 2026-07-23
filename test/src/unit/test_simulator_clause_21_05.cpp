// §21.5 Writing memory array data to a file — $writememb / $writememh dump a
// memory array's contents to a file the matching $readmemb / $readmemh can
// load back, and an existing file is overwritten (no append mode).
//
// Every rule here depends on how its input is produced: the memory operand is
// an unpacked array declared per §7.4.3, and the observable is the dumped file
// (or that file reloaded through §21.4's read tasks). These tests therefore
// declare real memories in module source and drive each call through the full
// pipeline (parse -> elaborate -> lower -> run), then inspect the file on disk
// or the round-tripped values — never hand-registering array state on a bare
// simulation context.
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

// §21.5: $writememh dumps the memory's words to a file $readmemh can load
// back: the round trip through a second array reproduces every word, and the
// file itself holds one hexadecimal word per line in address order.
TEST(WritememSim, WritememhDumpReloadsThroughReadmemh) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_rt_h.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] src [0:3];\n"
      "  logic [7:0] dst [0:3];\n"
      "  initial begin\n"
      "    src[0] = 8'h12; src[1] = 8'h34;\n"
      "    src[2] = 8'h56; src[3] = 8'h78;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%h %h %h %h\", dst[0], dst[1], dst[2], dst[3]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "12 34 56 78\n");
  EXPECT_EQ(SlurpFile(path), "12\n34\n56\n78\n");
  std::remove(path.c_str());
}

// §21.5: $writememb writes the words in binary — the radix its companion
// $readmemb expects ("respectively"). A word carrying an x bit is dumped with
// per-bit fidelity only the binary form can express, and reloads intact.
TEST(WritememSim, WritemembDumpReloadsThroughReadmemb) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_rt_b.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] src [0:2];\n"
      "  logic [7:0] dst [0:2];\n"
      "  initial begin\n"
      "    src[0] = 8'b00000001; src[1] = 8'b1010101x;\n"
      "    src[2] = 8'b11110000;\n"
      "    $writememb(\"" +
          path +
          "\", src);\n"
          "    $readmemb(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%b %b %b\", dst[0], dst[1], dst[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "00000001 1010101x 11110000\n");
  EXPECT_EQ(SlurpFile(path), "00000001\n1010101x\n11110000\n");
  std::remove(path.c_str());
}

// §21.5: a 4-state memory may hold fully-unknown or high-impedance words; the
// hexadecimal dump renders them as x / z digits $readmemh accepts, so the
// round trip preserves them.
TEST(WritememSim, WritememhPreservesUnknownAndHighZWords) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_xz.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] src [0:2];\n"
      "  logic [7:0] dst [0:2];\n"
      "  initial begin\n"
      "    src[0] = 8'h12; src[1] = 8'hxx; src[2] = 8'hzz;\n"
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
  EXPECT_EQ(out, "12 xx zz\n");
  std::remove(path.c_str());
}

// §21.5: words wider than a machine word dump and reload without truncation.
TEST(WritememSim, WideWordRoundTrip) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_wide.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [71:0] src [0:1];\n"
      "  logic [71:0] dst [0:1];\n"
      "  initial begin\n"
      "    src[0] = 72'h01_23456789_abcdef01;\n"
      "    src[1] = 72'hfe_dcba9876_54321098;\n"
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
  EXPECT_EQ(out, "0123456789abcdef01 fedcba987654321098\n");
  std::remove(path.c_str());
}

// §21.5: the file layout does not depend on the declaration's direction — a
// descending unpacked range still dumps its words from the low address upward,
// and the reload lands each word back at its original address.
TEST(WritememSim, DescendingDeclarationRoundTrip) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_desc.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] src [3:0];\n"
      "  logic [7:0] dst [3:0];\n"
      "  initial begin\n"
      "    src[0] = 8'ha0; src[1] = 8'ha1;\n"
      "    src[2] = 8'ha2; src[3] = 8'ha3;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%h %h %h %h\", dst[0], dst[1], dst[2], dst[3]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "a0 a1 a2 a3\n");
  EXPECT_EQ(SlurpFile(path), "a0\na1\na2\na3\n");
  std::remove(path.c_str());
}

// §21.5: when the named file already exists at the time of the call it is
// overwritten — there is no append mode. A file pre-created by the host with
// unrelated contents holds only the dump afterward.
TEST(WritememSim, OverwritesPreexistingHostFile) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_host.mem";
  {
    std::ofstream seed(path);
    seed << "stale sentinel contents\n";
  }
  RunCapture(
      "module t;\n"
      "  logic [7:0] m [0:0];\n"
      "  initial begin\n"
      "    m[0] = 8'h5a;\n"
      "    $writememh(\"" +
          path +
          "\", m);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "5a\n");
  std::remove(path.c_str());
}

// §21.5: a second dump to the same filename within one run likewise replaces
// the file: none of the first (longer) dump's words survive.
TEST(WritememSim, SecondDumpReplacesFirstWithinRun) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_replace.mem";
  RunCapture(
      "module t;\n"
      "  logic [7:0] big [0:3];\n"
      "  logic [7:0] lone [0:0];\n"
      "  initial begin\n"
      "    big[0] = 8'haa; big[1] = 8'hbb;\n"
      "    big[2] = 8'hcc; big[3] = 8'hdd;\n"
      "    lone[0] = 8'h11;\n"
      "    $writememb(\"" +
          path +
          "\", big);\n"
          "    $writememb(\"" +
          path +
          "\", lone);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "00010001\n");
  std::remove(path.c_str());
}

// §21.5 (Syntax 21-13): start_addr and finish_addr bound the words written,
// and a finish below the start dumps them in descending address order.
TEST(WritememSim, StartAndFinishBoundAndOrderTheDump) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_range.mem";
  RunCapture(
      "module t;\n"
      "  logic [7:0] src [0:4];\n"
      "  initial begin\n"
      "    src[0] = 8'h10; src[1] = 8'h11; src[2] = 8'h12;\n"
      "    src[3] = 8'h13; src[4] = 8'h14;\n"
      "    $writememh(\"" +
          path +
          "\", src, 3, 1);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "13\n12\n11\n");
  std::remove(path.c_str());
}

// §21.5 (Syntax 21-13): the production nests finish_addr inside start_addr, so
// the three-argument form is legal on its own; the dump then runs from
// start_addr through the end of the memory.
TEST(WritememSim, StartWithoutFinishRunsToArrayEnd) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_start.mem";
  RunCapture(
      "module t;\n"
      "  logic [7:0] src [0:3];\n"
      "  initial begin\n"
      "    src[0] = 8'h20; src[1] = 8'h21;\n"
      "    src[2] = 8'h22; src[3] = 8'h23;\n"
      "    $writememh(\"" +
          path +
          "\", src, 2);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "22\n23\n");
  std::remove(path.c_str());
}

// §21.5 (Syntax 21-13): the address operands are ordinary expressions — here a
// parameter and a localparam supply the bounds.
TEST(WritememSim, AddressBoundsFromParameterAndLocalparam) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_param.mem";
  RunCapture(
      "module t;\n"
      "  parameter int S = 3;\n"
      "  localparam int F = 1;\n"
      "  logic [7:0] src [0:4];\n"
      "  initial begin\n"
      "    src[0] = 8'h10; src[1] = 8'h11; src[2] = 8'h12;\n"
      "    src[3] = 8'h13; src[4] = 8'h14;\n"
      "    $writememh(\"" +
          path +
          "\", src, S, F);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "13\n12\n11\n");
  std::remove(path.c_str());
}

// §21.5 (Syntax 21-13): the bounds may equally be a runtime variable and an
// arithmetic expression over it.
TEST(WritememSim, AddressBoundsFromVariableAndExpression) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_varexpr.mem";
  RunCapture(
      "module t;\n"
      "  int s;\n"
      "  logic [7:0] src [0:3];\n"
      "  initial begin\n"
      "    src[0] = 8'h10; src[1] = 8'h11;\n"
      "    src[2] = 8'h12; src[3] = 8'h13;\n"
      "    s = 1;\n"
      "    $writememh(\"" +
          path +
          "\", src, s, s + 1);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "11\n12\n");
  std::remove(path.c_str());
}

// §21.5 (Syntax 21-13): the filename operand need not be a literal — a
// string-typed variable holding the path names the same file, exactly as on
// the §21.4 read side.
TEST(WritememSim, FilenameFromStringVariable) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_strfn.mem";
  RunCapture(
      "module t;\n"
      "  string fn;\n"
      "  logic [7:0] m [0:1];\n"
      "  initial begin\n"
      "    m[0] = 8'hc3; m[1] = 8'hd4;\n"
      "    fn = \"" +
          path +
          "\";\n"
          "    $writememh(fn, m);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "c3\nd4\n");
  std::remove(path.c_str());
}

// §21.5 (Syntax 21-13): the third filename form — an integral value whose
// packed bytes spell the path — names the same file as the literal would.
TEST(WritememSim, FilenameFromIntegralValue) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_intfn.mem";
  RunCapture(
      "module t;\n"
      "  reg [255:0] fnbits;\n"
      "  logic [7:0] m [0:1];\n"
      "  initial begin\n"
      "    m[0] = 8'he5; m[1] = 8'hf6;\n"
      "    fnbits = \"" +
          path +
          "\";\n"
          "    $writememh(fnbits, m);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "e5\nf6\n");
  std::remove(path.c_str());
}

// Negative form: a filename that cannot be opened (its directory does not
// exist) produces no dump, and the run continues past the failed call.
TEST(WritememSim, UnopenablePathLeavesRunAlive) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_no_such_dir/out.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] m [0:0];\n"
      "  initial begin\n"
      "    m[0] = 8'h01;\n"
      "    $writememh(\"" +
          path +
          "\", m);\n"
          "    $display(\"alive\");\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "alive\n");
  EXPECT_FALSE(std::ifstream(path).good());
}

// Negative form: the second operand must name a memory; a plain literal in the
// memory_name position dumps nothing — no file is created — and the run
// continues.
TEST(WritememSim, NonMemoryNameOperandWritesNothing) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_notmem.mem";
  std::remove(path.c_str());
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $writememh(\"" +
          path +
          "\", 8'h55);\n"
          "    $display(\"alive\");\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "alive\n");
  EXPECT_FALSE(std::ifstream(path).good());
}

}  // namespace
