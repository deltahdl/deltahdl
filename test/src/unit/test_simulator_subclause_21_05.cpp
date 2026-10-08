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
#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

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

// §21.5 with §7.4.2: a bound may be negative, and every word of the memory
// is dumped, here a one-dimensional memory whose bounds straddle zero. The walk
// from its low address reached an address past the last element's name.
TEST(WritememSim, AOneDimensionalMemoryStraddlingZeroIsDumpedWhole) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_neg_one.mem";
  RunCapture(
      "module t;\n"
      "  logic [7:0] m [-1:0];\n"
      "  initial begin\n"
      "    m[-1] = 8'h11; m[0] = 8'h22;\n"
      "    $writememh(\"" +
          path +
          "\", m);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "11\n22\n");
  std::remove(path.c_str());
}

// §21.5 with §7.4.2 and §21.4.3: a multidimensional memory with a negative
// bound is dumped in row-major order and reloaded through $readmemh word for
// word, and a block's own such array holds what is written to it. Its leaves
// were named apart from the indices every select and both tasks name, so the
// writes were lost and the dump empty.
TEST(WritememSim, AMultidimensionalMemoryWithANegativeBoundIsDumpedWhole) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_neg_multi.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] m [0:1][-1:0];\n"
      "  logic [7:0] r [0:1][-1:0];\n"
      "  initial begin : blk\n"
      "    logic [7:0] b [-1:0][0:1];\n"
      "    m[0][-1] = 8'h11; m[0][0] = 8'h22;\n"
      "    m[1][-1] = 8'h33; m[1][0] = 8'h44;\n"
      "    b[-1][1] = 8'h55;\n"
      "    $writememh(\"" +
          path +
          "\", m);\n"
          "    $readmemh(\"" +
          path +
          "\", r);\n"
          "    $display(\"%h %h %h %h %h\", r[0][-1], r[0][0], r[1][-1], "
          "r[1][0], b[-1][1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "11\n22\n33\n44\n");
  EXPECT_EQ(out, "11 22 33 44 55\n");
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

// §21.5: the second operand must name a memory array; a plain literal in the
// memory_name position is reported under 21.5 and dumps nothing -- no file is
// created -- and the run continues.
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$writememh: memory_name is not an unpacked array",
                            3, "21.5"));
}

// §21.5 with §8.5: the memory is any unpacked array, a class object's array
// property included. Named bare inside the object's own methods, it is loaded
// by $readmemh and dumped by $writememh, and the dump loads back into another
// object's property named through a handle.
TEST(WritememSim, ArrayPropertyNamedInAMethodIsDumped) {
  SimFixture f;
  std::string in_path = "/tmp/deltahdl_t2105_prop_in.mem";
  std::string out_path = "/tmp/deltahdl_t2105_prop_out.mem";
  SeedFile(in_path, "aa bb cc\n");
  std::string out = RunCapture(
      "module t;\n"
      "  class Mem;\n"
      "    logic [7:0] data[0:2];\n"
      "    function void load(string f); $readmemh(f, data); endfunction\n"
      "    function void save(string f); $writememh(f, data); endfunction\n"
      "  endclass\n"
      "  Mem m1, m2;\n"
      "  initial begin\n"
      "    m1 = new;\n"
      "    m1.load(\"" +
          in_path +
          "\");\n"
          "    $display(\"%h %h %h\", m1.data[0], m1.data[1], m1.data[2]);\n"
          "    m1.save(\"" +
          out_path +
          "\");\n"
          "    m2 = new;\n"
          "    $readmemh(\"" +
          out_path +
          "\", m2.data);\n"
          "    $display(\"%h %h %h\", m2.data[0], m2.data[1], m2.data[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "aa bb cc\naa bb cc\n");
  EXPECT_EQ(SlurpFile(out_path), "aa\nbb\ncc\n");
  std::remove(in_path.c_str());
  std::remove(out_path.c_str());
}

// §21.5 with §23.6: the memory dumped may be an instance's array named through
// a hierarchical reference.
TEST(WritememSim, HierarchicallyNamedArrayIsDumped) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_hier.mem";
  std::string out = RunCapture(
      "module sub; logic [7:0] mem[0:1]; endmodule\n"
      "module t;\n"
      "  sub u();\n"
      "  initial begin\n"
      "    u.mem[0] = 8'hab; u.mem[1] = 8'hcd;\n"
      "    $writememh(\"" +
          path +
          "\", u.mem);\n"
          "    $display(\"done\");\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "done\n");
  EXPECT_EQ(SlurpFile(path), "ab\ncd\n");
  std::remove(path.c_str());
}

// §21.5 (Syntax 21-13) with §7.10: a queue is dumped through the same address
// window as a fixed array, so a finish below the start writes its elements
// from the start index down.
TEST(WritememSim, QueueWindowDescendsWhenFinishIsBelowStart) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_q_desc.mem";
  RunCapture(
      "module t;\n"
      "  logic [7:0] q [$];\n"
      "  initial begin\n"
      "    q.push_back(8'h0a); q.push_back(8'h0b); q.push_back(8'h0c);\n"
      "    $writememh(\"" +
          path +
          "\", q, 2, 0);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "0c\n0b\n0a\n");
  std::remove(path.c_str());
}

// §21.5 with §7.10: a window reaching past both ends of a queue writes the
// elements the queue holds and nothing for the indices it does not; a
// longint start of -1 puts the window's first address below index 0.
TEST(WritememSim, QueueWindowPastBothEndsWritesOnlyTheElements) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_q_wide.mem";
  RunCapture(
      "module t;\n"
      "  logic [7:0] q [$];\n"
      "  longint first = -1;\n"
      "  initial begin\n"
      "    q.push_back(8'h0a); q.push_back(8'h0b);\n"
      "    $writememh(\"" +
          path +
          "\", q, first, 3);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "0a\n0b\n");
  std::remove(path.c_str());
}

// §21.5 with §7.10: an empty queue has no words, so its dump is a file with
// nothing in it -- created, as every $writemem call creates its file.
TEST(WritememSim, EmptyQueueDumpsAnEmptyFile) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_q_empty.mem";
  std::remove(path.c_str());
  RunCapture(
      "module t;\n"
      "  logic [7:0] q [$];\n"
      "  initial $writememh(\"" +
          path +
          "\", q);\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(std::ifstream(path).good());
  EXPECT_EQ(SlurpFile(path), "");
  std::remove(path.c_str());
}

// §21.5 with §21.4.3: start_addr and finish_addr address the highest
// dimension of a multidimensional array. A window from 3 down to 0 over
// m[1:2][0:1] skips the addresses outside 1..2 and writes the two rows in
// descending order, each row's words from its low index up.
TEST(WritememSim, MultiDimWindowDescendsAndSkipsAddressesOutsideIt) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_md_win.mem";
  RunCapture(
      "module t;\n"
      "  logic [7:0] m [1:2][0:1];\n"
      "  initial begin\n"
      "    m[1][0] = 8'h11; m[1][1] = 8'h12;\n"
      "    m[2][0] = 8'h21; m[2][1] = 8'h22;\n"
      "    $writememh(\"" +
          path +
          "\", m, 3, 0);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "21\n22\n11\n12\n");
  std::remove(path.c_str());
}

// §21.5: a window reaching below and above a fixed array's bounds writes the
// words at the addresses the array has and none for the others.
TEST(WritememSim, ArrayWindowPastBothBoundsWritesOnlyTheWords) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_arr_wide.mem";
  RunCapture(
      "module t;\n"
      "  logic [7:0] m [2:3];\n"
      "  initial begin\n"
      "    m[2] = 8'h22; m[3] = 8'h33;\n"
      "    $writememh(\"" +
          path +
          "\", m, 1, 4);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "22\n33\n");
  std::remove(path.c_str());
}

// §21.5 with §8.5: a class's array property is dumped through the same
// window, so a window from 3 down to 0 over data[1:2] writes the property's
// two words in descending order and nothing for the addresses beyond them.
TEST(WritememSim, ArrayPropertyWindowDescendsAndSkipsAddressesOutsideIt) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_prop_win.mem";
  RunCapture(
      "module t;\n"
      "  class Mem;\n"
      "    logic [7:0] data[1:2];\n"
      "  endclass\n"
      "  Mem m;\n"
      "  initial begin\n"
      "    m = new;\n"
      "    m.data[1] = 8'haa; m.data[2] = 8'hbb;\n"
      "    $writememh(\"" +
          path +
          "\", m.data, 3, 0);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "bb\naa\n");
  std::remove(path.c_str());
}

// §21.5 with §7.5 and §8.5: a dynamic array property not yet sized by new[]
// has no words, so its dump is an empty file.
TEST(WritememSim, UnsizedDynamicArrayPropertyDumpsAnEmptyFile) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_prop_empty.mem";
  std::remove(path.c_str());
  RunCapture(
      "module t;\n"
      "  class Mem;\n"
      "    logic [7:0] data[];\n"
      "  endclass\n"
      "  Mem m;\n"
      "  initial begin\n"
      "    m = new;\n"
      "    $writememh(\"" +
          path +
          "\", m.data);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(std::ifstream(path).good());
  EXPECT_EQ(SlurpFile(path), "");
  std::remove(path.c_str());
}

// Negative form for $writememb: a path that cannot be opened writes nothing,
// the warning names $writememb, the task the source called, and the run
// continues past the call.
TEST(WritememSim, UnopenablePathWarningNamesWritememb) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_no_such_dir/out_b.mem";
  testing::internal::CaptureStderr();
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] m [0:0];\n"
      "  initial begin\n"
      "    m[0] = 8'h01;\n"
      "    $writememb(\"" +
          path +
          "\", m);\n"
          "    $display(\"alive\");\n"
          "  end\n"
          "endmodule\n",
      f);
  std::string err = testing::internal::GetCapturedStderr();
  EXPECT_EQ(out, "alive\n");
  EXPECT_NE(err.find("$writememb: cannot open file: " + path),
            std::string::npos);
  EXPECT_FALSE(std::ifstream(path).good());
}

// §21.5 (Syntax 21-13): both tasks require a filename and a memory_name. A
// call giving only the filename is reported under 21.5 at the call, naming
// the task the source wrote, and the run continues past it.
TEST(WritememSim, ACallShortOfAMemoryNameIsReportedUnderEachTaskName) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $writememh(\"/tmp/deltahdl_t2105_short_h.mem\");\n"
      "    $writememb(\"/tmp/deltahdl_t2105_short_b.mem\");\n"
      "    $display(\"alive\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "alive\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$writememh takes a file name and a memory name, "
                            "and this call has fewer",
                            3, "21.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$writememb takes a file name and a memory name, "
                            "and this call has fewer",
                            4, "21.5"));
}

// §21.5 with §26.3: a package's memory array, named through the package that
// declares it, is dumped like a module's.
TEST(WritememSim, PackageQualifiedArrayIsDumped) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_pkg.mem";
  RunCapture(
      "package p;\n"
      "  logic [7:0] mem [0:1];\n"
      "endpackage\n"
      "module t;\n"
      "  initial begin\n"
      "    p::mem[0] = 8'h12; p::mem[1] = 8'h34;\n"
      "    $writememh(\"" +
          path +
          "\", p::mem);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "12\n34\n");
  std::remove(path.c_str());
}

// §21.5: a plain variable is not a memory array, so naming one as the
// memory_name is reported under 21.5 at the operand, and a file already at
// the path keeps the contents it had.
TEST(WritememSim, PlainVariableMemoryNameIsReportedAndFileKept) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t2105_plain.mem";
  SeedFile(path, "kept\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] r = 8'h5a;\n"
      "  initial begin\n"
      "    $writememb(\"" +
          path +
          "\", r);\n"
          "    $display(\"alive\");\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "alive\n");
  EXPECT_EQ(SlurpFile(path), "kept\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$writememb: memory_name is not an unpacked array",
                            4, "21.5"));
  std::remove(path.c_str());
}

}  // namespace
