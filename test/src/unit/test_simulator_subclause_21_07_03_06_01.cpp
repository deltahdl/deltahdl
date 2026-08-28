#include <cctype>
#include <string>
#include <utility>
#include <vector>

// Completes the CoverageDB type that sim_context.h only forward-declares;
// included with the fixtures so SimContext's inline constructor (whose unwind
// path destroys the owned coverage database) is well-formed in this TU.
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "fixture_vcd_dump_from_source.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_text_lines.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.3.6.1: the $vcdclose keyword command. Whether the keyword appears at
// all follows from how the dump was opened (the extended dump task of
// §21.7.3.1 is what makes the file extended), and the time it records is the
// end time the simulation actually reached -- both are properties of a full
// run, so each test drives real source through parse, elaboration, lowering,
// and the scheduler with the driver's per-timestep recording loop installed,
// then reads the file back after the close.
class VcdcloseKeyword : public VcdDumpRunTestBase {
 protected:
  // Runs a single-module source through the full pipeline with the driver's
  // dump loop and returns the dump file contents. `close_file` mirrors the
  // simulation driver's final step of handing the writer the end simulation
  // time as the file is closed (the branch main.cpp runs after the scheduler
  // finishes); with it off the run ends without that close step.
  std::string RunVcd(const std::string& src, bool close_file = true) {
    return RunVcdDump(src, {.scope = "t", .close_file = close_file});
  }
};
// Syntax 21-26 / the example's rendering: the closed extended file ends with
// the three-token command "$vcdclose <final_simulation_time> $end", where the
// time takes the value-change timestamp form -- '#' followed by decimal
// digits only. The command's position is part of the claim: the keyword marks
// the file's close, so nothing follows its $end, and one close writes it
// exactly once.
TEST_F(VcdcloseKeyword, ClosedFileEndsWithKeywordTimeEnd) {
  auto toks =
      Tokens(RunVcd("module t;\n"
                    "  logic a;\n"
                    "  initial begin\n"
                    "    a = 1'b0;\n"
                    "    $dumpports(, \"dump2.dump\");\n"
                    "    #10 a = 1'b1;\n"
                    "  end\n"
                    "endmodule\n"));
  ASSERT_GE(toks.size(), 3u);
  EXPECT_EQ(toks[toks.size() - 3], "$vcdclose");
  EXPECT_EQ(toks[toks.size() - 1], "$end");
  const std::string& time_tok = toks[toks.size() - 2];
  ASSERT_GE(time_tok.size(), 2u);
  EXPECT_EQ(time_tok[0], '#');
  for (size_t i = 1; i < time_tok.size(); ++i) {
    EXPECT_TRUE(std::isdigit(static_cast<unsigned char>(time_tok[i])))
        << "non-decimal digit in final_simulation_time: " << time_tok;
  }
  // The run's own end time is what the timestamp carries.
  EXPECT_EQ(time_tok, "#10");
  EXPECT_EQ(CountToken(toks, "$vcdclose"), 1u);
}

// The recorded time is the end simulation time, not the last value-change
// time: the run's last timestep only rewrites a's existing value, so no
// change is recorded there, yet the close still stamps that later time. This
// is the "regardless of the state of signal changes" semantics -- a parser
// relying on value changes alone would misread the end time as #10.
TEST_F(VcdcloseKeyword, RecordsEndTimeBeyondLastValueChange) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "    #5 a = 1'b1;\n"  // a write with no value change at the end time
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #15 $end"), std::string::npos);
  EXPECT_EQ(content.find("$vcdclose #10"), std::string::npos);
}

// End-time edge: a run whose whole life is simulation time zero closes with
// #0 -- the decimal form has no special case for the origin.
TEST_F(VcdcloseKeyword, ZeroTimeRunClosesWithZero) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #0 $end"), std::string::npos);
}

// The extended-ness the keyword follows from is the dump task's execution,
// whatever form its call takes (§21.7.3.1): the no-argument default-named
// form still yields a file that closes with the keyword.
TEST_F(VcdcloseKeyword, DefaultNamedDumpAlsoCloses) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #10 $end"), std::string::npos);
}

// Filename held in a string variable (declaration initializer form): the
// resolved-name machinery of the dump task changes nothing about the close --
// the keyword and its end time land all the same.
TEST_F(VcdcloseKeyword, StringVariableFilenameFormAlsoCloses) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  string fn = \"dump2.dump\";\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, fn);\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #10 $end"), std::string::npos);
}

// Filename held in an integral variable assigned procedurally (kept within
// four characters so the character string survives the integral width): the
// remaining filename data type the dump task admits, closing identically.
TEST_F(VcdcloseKeyword, IntegralVariableFilenameFormAlsoCloses) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  int fn;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    fn = \"du2\";\n"
      "    $dumpports(, fn);\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #10 $end"), std::string::npos);
}

// Filename held in a string variable assigned procedurally before the dump
// task runs: the other assignment position for the string-typed name, closing
// identically.
TEST_F(VcdcloseKeyword, ProceduralStringFilenameFormAlsoCloses) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  string fn;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    fn = \"dump2.dump\";\n"
      "    $dumpports(, fn);\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #10 $end"), std::string::npos);
}

// Filename held in an integral variable given its character string in the
// declaration initializer: the other assignment position for the integral
// name, closing identically.
TEST_F(VcdcloseKeyword, DeclInitIntegralFilenameFormAlsoCloses) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  int fn = \"du2\";\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, fn);\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #10 $end"), std::string::npos);
}

// Filename supplied by a module parameter (kept within four characters so the
// untyped parameter's integral value holds the whole character string): the
// remaining constant form for the name of the file the close stamps.
TEST_F(VcdcloseKeyword, ParameterFilenameFormAlsoCloses) {
  auto content = RunVcd(
      "module t;\n"
      "  parameter FN = \"du2\";\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, FN);\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #10 $end"), std::string::npos);
}

// Syntactic position of the extending task: reached from an edge-triggered
// always process mid-run rather than an initial block, the file it makes
// extended still closes with the keyword stamping the run's own end time.
TEST_F(VcdcloseKeyword, DumpportsFromAlwaysStillCloses) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic go;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    go = 1'b0;\n"
      "    #5 go = 1'b1;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "  always @(posedge go) $dumpports(, \"dump2.dump\");\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #15 $end"), std::string::npos);
}

// Remaining syntactic position for the extending call: enabled from a task
// body, the file still closes with the keyword carrying the run's end time.
TEST_F(VcdcloseKeyword, TaskBodyDumpportsStillCloses) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  task start_dump;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "  endtask\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    start_dump;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #10 $end"), std::string::npos);
}

// A run whose end time has the magnitude of the subclause's example renders
// it as plain decimal digits after the '#': no grouping, no base prefix,
// exactly the timestamp form the shorter runs showed.
TEST_F(VcdcloseKeyword, ExampleScaleEndTimeRendersDecimal) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #13000 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #13000 $end"), std::string::npos);
}

// The dump task may execute several times (all at one simulation time, each
// naming a distinct file -- here a string literal and a constant localparam
// name); the close is still a single event, so the keyword appears exactly
// once and stamps the one end time.
TEST_F(VcdcloseKeyword, MultipleDumpportsCallsStillCloseOnce) {
  auto toks =
      Tokens(RunVcd("module t;\n"
                    "  logic a;\n"
                    "  localparam FN = \"dux\";\n"
                    "  initial begin\n"
                    "    a = 1'b0;\n"
                    "    $dumpports(, \"dump2.dump\");\n"
                    "    $dumpports(, FN);\n"
                    "    #10 a = 1'b1;\n"
                    "  end\n"
                    "endmodule\n"));
  EXPECT_EQ(CountToken(toks, "$vcdclose"), 1u);
  ASSERT_GE(toks.size(), 3u);
  EXPECT_EQ(toks[toks.size() - 3], "$vcdclose");
  EXPECT_EQ(toks[toks.size() - 2], "#10");
  EXPECT_EQ(toks[toks.size() - 1], "$end");
}

// Negative: the keyword belongs to the extended format. A 4-state dump --
// opened by $dumpfile/$dumpvars, never by the extended task -- runs the same
// driver close step yet gains no $vcdclose.
TEST_F(VcdcloseKeyword, FourStateDumpNeverGainsVcdclose) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    $dumpvars;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(content.find("#10"), std::string::npos);  // the dump did record
  EXPECT_EQ(content.find("$vcdclose"), std::string::npos);
}

// Negative: the keyword marks the close itself. An extended run whose file is
// released without the driver's close step leaves no $vcdclose behind -- the
// keyword is not written ahead of time during dumping.
TEST_F(VcdcloseKeyword, NoKeywordWithoutCloseStep) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      /*close_file=*/false);
  ASSERT_NE(content.find("#10"), std::string::npos);  // the dump did record
  EXPECT_EQ(content.find("$vcdclose"), std::string::npos);
}

// §21.7.3.6.1 edge, genuinely confined to the writer stage: closing is
// harmless when no dump file was ever opened. The emit path guards on an open
// output stream, so an extended writer whose file failed to open writes
// nothing and does not fault. The destination sits under an existing regular
// file so the stream cannot open; no run produced this state, so no source
// drives it.
TEST_F(VcdcloseKeyword, WithoutOpenFileIsHarmless) {
  VcdWriter vcd(tmp_path_ + "/cannot_open.vcd");
  ASSERT_FALSE(vcd.IsOpen());
  vcd.SetExtended();
  vcd.WriteVcdClose(13000);
  EXPECT_FALSE(vcd.IsOpen());
}

// §21.7.3.6.1 again, with the source issuing the command instead of the
// simulation driver. Every case above takes the command from the fixture:
// VcdDumpRunTestBase::RunVcdDump calls WriteVcdClose itself when close_file is
// set, so those cases observe the command's form and none of them can observe
// what a source's own $vcdclose call does. These cases supply the source and
// nothing else -- no writer is installed and the fixture's closing step is off
// -- so the only thing that can put a close command in the file is the task
// the source called (deltahdl/deltahdl#3254).
class VcdcloseFromSource : public VcdDumpFromSourceTestBase {
 protected:
  // One design under either VCD task family and with or without the source's
  // own close, so the only difference between the cases below is which tasks
  // they insert. The close stands at a simulation time of its own: the dump is
  // opened at time 0 and the run goes on to time 15, while §21.7.3.6.1 records
  // "the final simulation time at the time the extended VCD file is closed",
  // which is neither of those. A command carrying 0 or 15 would therefore be
  // recording something other than what the clause asks for.
  static std::string DesignCalling(const std::string& open_task,
                                   const std::string& close_task) {
    return "module t;\n"
           "  logic a;\n"
           "  initial begin\n"
           "    a = 1'b0;\n" +
           open_task + "    #10 a = 1'b1;\n" + close_task +
           "    #5 a = 1'b0;\n"
           "  end\n"
           "endmodule\n";
  }
};

// §21.7.3.6.1: "The $vcdclose keyword indicates the final simulation time at
// the time the extended VCD file is closed." A source calling the task gets
// that command written into the extended file its $dumpports opened, carrying
// the time the call executed at. The keyword terminates the file, so it stands
// last and stands once: the value change the run makes at time 15 is not
// recorded after it, and no second close is stamped with a later time.
TEST_F(VcdcloseFromSource, SourceCallTerminatesTheExtendedFileAtItsOwnTime) {
  RunSource(DesignCalling("    $dumpports(, \"portdump.vcd\");\n",
                          "    $vcdclose;\n"),
            /*close_file=*/false);

  auto content = DumpFile("portdump.vcd");
  // §21.7.3.1 puts the opening checkpoint at the end of the time unit the dump
  // task executed in, one time unit before the close, so the dump was recording
  // by the time the file was closed. Without this the claims below would hold
  // just as well of a file nothing was ever dumped into.
  EXPECT_TRUE(HasLine(Lines(content), "$dumpports"));
  auto toks = Tokens(content);
  ASSERT_GE(toks.size(), 3u);
  EXPECT_EQ(toks[toks.size() - 3], "$vcdclose");
  EXPECT_EQ(toks[toks.size() - 2], "#10");
  EXPECT_EQ(toks[toks.size() - 1], "$end");
  EXPECT_EQ(CountToken(toks, "$vcdclose"), 1u);
}

// The complement, and what makes the case above a claim about the source's own
// call rather than about every extended dump: with the call taken out of the
// same design, nothing terminates the file. Without this case a simulator that
// wrote the command into every extended dump it released would satisfy the
// case above.
TEST_F(VcdcloseFromSource, ExtendedDumpWithoutTheCallIsNotTerminated) {
  RunSource(DesignCalling("    $dumpports(, \"portdump.vcd\");\n", ""),
            /*close_file=*/false);

  auto content = DumpFile("portdump.vcd");
  // The §21.7.4.2 node information and the value change of the run's last time
  // unit anchor the absence, which a run that created no file at all -- or one
  // whose dump stopped early -- would otherwise satisfy on its own.
  ASSERT_NE(content.find("$var port"), std::string::npos);
  ASSERT_TRUE(HasLine(Lines(content), "#15"));
  EXPECT_EQ(content.find("$vcdclose"), std::string::npos);
}

// §21.7.3.6: "Extended VCD provides one additional keyword command to that of
// the 4-state VCD." The keyword is what the extended format adds, so a 4-state
// file has no place for it however its source asks. §21.7.3.7 settles what the
// call does instead of leaving it unspecified: an extended VCD system task
// naming a file no $dumpports call opened "shall be ignored", and its
// no-argument form runs its default action over the files $dumpports opened,
// of which this run opened none. So the command is not written and the 4-state
// dump goes on recording.
TEST_F(VcdcloseFromSource, FourStateDumpIgnoresTheSourceCall) {
  RunSource(DesignCalling("    $dumpfile(\"vardump.vcd\");\n    $dumpvars;\n",
                          "    $vcdclose;\n"),
            /*close_file=*/false);

  auto content = DumpFile("vardump.vcd");
  // The §21.7.2.1 4-state node information anchors the absence below, which a
  // run that created no file at all would otherwise satisfy on its own.
  ASSERT_NE(content.find("$var wire"), std::string::npos);
  EXPECT_EQ(content.find("$vcdclose"), std::string::npos);
  // Ignored rather than obeyed: the value change of the time unit after the
  // call is recorded, so the dump the call could not close is still running.
  EXPECT_TRUE(HasLine(Lines(content), "#15"));
}

}  // namespace
}  // namespace delta
