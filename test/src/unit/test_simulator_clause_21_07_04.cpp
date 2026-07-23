#include <algorithm>
#include <iterator>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

// Completes the CoverageDB type that sim_context.h only forward-declares;
// included ahead of the fixtures so SimContext's inline constructor (whose
// unwind path destroys the owned coverage database) is well-formed in this TU.
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.4: format of the extended VCD file. The subclause's own text (its
// descendants own the extended grammar, the node information, and the value
// change section) makes three observable claims about the file as a whole:
// (C1) like the 4-state file, the extended file is structured as free format
// -- no command is tied to a line or column position, so tokenizing the file
// on white space alone recovers its command structure; (C2) white space
// separates the commands from one another; (C3) that separation leaves the
// file plain text a text editor can display. All three are runtime rules
// about the file the extended dump leaves on disk, so each test drives real
// source -- using the $dumpports task family to mark the writer extended and
// to produce every kind of extended command -- through parse, elaboration,
// lowering, and the scheduler with the driver's per-timestep recording loop
// installed, then inspects the file.
class ExtendedVcdFileFormat : public VcdTestBase {
 protected:
  // Runs a single-module source through the full pipeline with the driver's
  // dump loop (timestamp + changed values at the end of each time unit) and
  // returns the dump file contents. The module scope is opened around the
  // variable definitions the way the simulation driver does, so the $scope
  // and $upscope commands are among the commands whose separation is checked.
  // `close_file` mirrors the driver's final step of handing the writer the
  // end simulation time as the file is closed; only a writer the source's
  // $dumpports call marked extended emits the close command.
  std::string RunVcd(const std::string& src, bool close_file = false) {
    SimFixture f;
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    {
      VcdWriter vcd(tmp_path_);
      vcd.WriteHeader("1ns");
      vcd.BeginScope("t");
      // Register in name order so identifier codes are deterministic: the
      // alphabetically first variable gets '!', the next '"', and so on.
      std::vector<std::pair<std::string_view, Variable*>> vars(
          f.ctx.GetVariables().begin(), f.ctx.GetVariables().end());
      std::sort(vars.begin(), vars.end(),
                [](const auto& a, const auto& b) { return a.first < b.first; });
      for (const auto& [name, var] : vars) {
        vcd.RegisterSignal(name, var->value.width, var);
      }
      vcd.EndScope();
      vcd.EndDefinitions();
      // Value change dumping starts once the source's extended dump task
      // executes and produces its opening checkpoint.
      vcd.ArmDumpvarsStart();
      f.ctx.SetVcdWriter(&vcd);
      f.scheduler.SetPostTimestepCallback([&vcd, &f]() {
        vcd.WriteTimestamp(f.ctx.CurrentTime().ticks);
        vcd.DumpChangedValues(0);
      });
      f.scheduler.Run();
      if (close_file) vcd.WriteVcdClose(f.ctx.CurrentTime().ticks);
    }  // writer destructor flushes the dump to tmp_path_ before ReadVcd
    return ReadVcd();
  }
};

// The dump file split into its white-space-delimited tokens. Free format
// means this projection alone -- no line or column information -- is enough
// to recover every command.
std::vector<std::string> Tokens(const std::string& content) {
  std::istringstream iss(content);
  return {std::istream_iterator<std::string>(iss),
          std::istream_iterator<std::string>()};
}

// True when no token fuses two commands together: a '$' introduces a keyword
// command, so after tokenizing on white space it can only appear at the start
// of a token. A writer that ran two commands together (for example $end
// immediately followed by a checkpoint keyword, or a value change flushed
// against $end) would leave a token with an interior '$'.
bool NoFusedCommands(const std::vector<std::string>& toks) {
  for (const auto& t : toks) {
    if (t.find('$', 1) != std::string::npos) return false;
  }
  return true;
}

// Occurrences of `target` as a complete white-space-delimited token.
size_t CountToken(const std::vector<std::string>& toks,
                  std::string_view target) {
  size_t n = 0;
  for (const auto& t : toks) {
    if (t == target) ++n;
  }
  return n;
}

// Every keyword that opens a $end-closed section in the files these tests
// produce: the 4-state vocabulary the extended file inherits plus the
// extended-only close command.
size_t CountSectionOpeners(const std::vector<std::string>& toks) {
  const char* openers[] = {
      "$date",    "$version", "$timescale",      "$scope",    "$var",
      "$upscope", "$comment", "$enddefinitions", "$dumpvars", "$dumpall",
      "$dumpoff", "$dumpon",  "$vcdclose"};
  size_t opened = 0;
  for (const char* kw : openers) opened += CountToken(toks, kw);
  return opened;
}

// The dump file split into lines, so the one-command-per-line rendering the
// separation rule produces can be observed directly.
std::vector<std::string> Lines(const std::string& content) {
  std::vector<std::string> out;
  std::string cur;
  for (char c : content) {
    if (c == '\n') {
      out.push_back(cur);
      cur.clear();
    } else {
      cur.push_back(c);
    }
  }
  if (!cur.empty()) out.push_back(cur);
  return out;
}

bool HasLine(const std::vector<std::string>& lines, std::string_view target) {
  for (const auto& l : lines) {
    if (l == target) return true;
  }
  return false;
}

// C2 over the declaration commands of an extended file: with a scalar, a
// vector, and a real variable dumped through $dumpports, every declaration
// keyword the header and node information carry ($date, $version, $timescale,
// $scope, $var, $upscope, $enddefinitions, and the $end closing each section)
// stands apart as its own white-space-delimited token, and no token anywhere
// fuses two commands.
TEST_F(ExtendedVcdFileFormat, DeclarationCommandsStandApartAsTokens) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [3:0] v;\n"
      "  real r;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    v = 4'b0000;\n"
      "    r = 3.5;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  ASSERT_FALSE(toks.empty());
  EXPECT_GE(CountToken(toks, "$date"), 1u);
  EXPECT_GE(CountToken(toks, "$version"), 1u);
  EXPECT_GE(CountToken(toks, "$timescale"), 1u);
  EXPECT_GE(CountToken(toks, "$scope"), 1u);
  EXPECT_EQ(CountToken(toks, "$var"), 3u);  // a, r, v each get a definition
  EXPECT_GE(CountToken(toks, "$upscope"), 1u);
  EXPECT_EQ(CountToken(toks, "$enddefinitions"), 1u);
  EXPECT_GE(CountToken(toks, "$end"), 1u);
  EXPECT_TRUE(NoFusedCommands(toks));
  // The real variable's recorded value is itself a command bounded by white
  // space like the rest: the opening checkpoint renders it on a line of its
  // own (a -> '!', r -> '"', v -> '#').
  EXPECT_TRUE(HasLine(Lines(content), "r3.5 \""));
}

// C2 over the simulation commands: with the extended checkpoint tasks of the
// $dumpports family all executed from real source, each checkpoint keyword
// section the dumper writes is introduced by a standalone token, every
// simulation-time command is a '#' immediately followed by decimal digits and
// nothing else, and no two commands are ever juxtaposed without white space.
TEST_F(ExtendedVcdFileFormat, SimulationCommandsStandApartAsTokens) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "    #10 $dumpportsall;\n"
      "    #10 $dumpportsoff;\n"
      "    #10 $dumpportson;\n"
      "    #10 a = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  EXPECT_EQ(CountToken(toks, "$dumpvars"), 1u);  // opening checkpoint
  EXPECT_EQ(CountToken(toks, "$dumpall"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpoff"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpon"), 1u);
  for (const auto& t : toks) {
    if (t[0] != '#') continue;
    ASSERT_GT(t.size(), 1u) << "bare # token";
    for (size_t i = 1; i < t.size(); ++i) {
      ASSERT_TRUE(t[i] >= '0' && t[i] <= '9')
          << "simulation time fused with another command: " << t;
    }
  }
  EXPECT_EQ(content.find("$end$"), std::string::npos);
  EXPECT_TRUE(NoFusedCommands(toks));
}

// C2 between value changes, and its boundary: when a scalar and a vector both
// change in one time unit of the extended dump, the timestamp and the two
// value-change commands are each separated from their neighbors (rendered one
// command per line). The separation applies BETWEEN commands only -- the
// scalar change itself stays one unsplit token, since its interior belongs to
// the command.
TEST_F(ExtendedVcdFileFormat, ValueChangeCommandsSeparatedFromNeighbors) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    v = 4'b0000;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 begin a = 1'b1; v = 4'b1010; end\n"
      "  end\n"
      "endmodule\n");
  auto lines = Lines(content);
  // a -> '!', v -> '"': timestamp and both same-time changes each occupy a
  // white-space-bounded command of their own.
  EXPECT_TRUE(HasLine(lines, "#10"));
  EXPECT_TRUE(HasLine(lines, "1!"));
  EXPECT_TRUE(HasLine(lines, "b1010 \""));
  // The scalar change is one command: the separation rule does not reach
  // inside it, so it tokenizes as a single unit.
  auto toks = Tokens(content);
  EXPECT_GE(CountToken(toks, "1!"), 1u);
}

// C1 (free format): white-space tokenization alone -- with every line and
// column position discarded -- recovers the command structure of the extended
// file. Each section-opening keyword is closed by a matching standalone $end
// token, and the single-token commands pair up adjacently ($upscope $end,
// $enddefinitions $end) in the token stream.
TEST_F(ExtendedVcdFileFormat, WhitespaceTokenizationRecoversCommandStructure) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "    #10 $dumpportsall;\n"
      "    #10 $dumpportsoff;\n"
      "    #10 $dumpportson;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  ASSERT_FALSE(toks.empty());
  EXPECT_EQ(CountToken(toks, "$end"), CountSectionOpeners(toks));
  for (size_t i = 0; i + 1 < toks.size(); ++i) {
    if (toks[i] == "$upscope" || toks[i] == "$enddefinitions") {
      EXPECT_EQ(toks[i + 1], "$end") << "after " << toks[i];
    }
  }
}

// C2 over a dumper-inserted command: the $comment section the dumper itself
// inserts when the ports dump reaches its size limit joins the extended file
// as a white-space-separated command like any other -- $comment is a
// standalone token, nothing fuses, and the opener/$end pairing still
// balances.
TEST_F(ExtendedVcdFileFormat, DumperInsertedCommentIsSeparatedCommand) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 data = 8'h91;\n"
      "    #10 $dumpportslimit(1);\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  EXPECT_EQ(CountToken(toks, "$comment"), 1u);
  EXPECT_TRUE(NoFusedCommands(toks));
  EXPECT_EQ(CountToken(toks, "$end"), CountSectionOpeners(toks));
}

// C2 over the extended-only close command: when the driver hands the writer
// the end simulation time as the file is closed, the resulting close command
// is a keyword section like the rest -- introduced by a standalone token,
// its recorded final time keeps the #<decimal> form, and the opener/$end
// pairing balances across the whole file.
TEST_F(ExtendedVcdFileFormat, CloseCommandJoinsFileAsSeparatedSection) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      /*close_file=*/true);
  auto toks = Tokens(content);
  EXPECT_EQ(CountToken(toks, "$vcdclose"), 1u);
  EXPECT_TRUE(NoFusedCommands(toks));
  EXPECT_EQ(CountToken(toks, "$end"), CountSectionOpeners(toks));
  for (const auto& t : toks) {
    if (t[0] != '#') continue;
    ASSERT_GT(t.size(), 1u) << "bare # token";
    for (size_t i = 1; i < t.size(); ++i) {
      ASSERT_TRUE(t[i] >= '0' && t[i] <= '9')
          << "final simulation time fused with another command: " << t;
    }
  }
}

// The producing task is an ordinary task enable: moved into a task body, the
// same run yields an extended file with the same separation properties -- the
// command text depends on what was dumped, not on the syntactic position of
// the task that produced it.
TEST_F(ExtendedVcdFileFormat, TaskBodyProducedCommandsKeepSeparation) {
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
  auto toks = Tokens(content);
  EXPECT_EQ(CountToken(toks, "$dumpvars"), 1u);
  EXPECT_EQ(CountToken(toks, "$enddefinitions"), 1u);
  EXPECT_TRUE(NoFusedCommands(toks));
}

// The producing task can equally be reached from an always process: an
// edge-triggered $dumpports opens the dump mid-simulation, and the file it
// leaves keeps the free-format command separation -- the checkpoint, the
// later timestamp, and the recorded change all stand apart as tokens.
TEST_F(ExtendedVcdFileFormat, AlwaysProducedCommandsKeepSeparation) {
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
  auto toks = Tokens(content);
  EXPECT_EQ(CountToken(toks, "$dumpvars"), 1u);
  EXPECT_GE(CountToken(toks, "#15"), 1u);
  EXPECT_TRUE(NoFusedCommands(toks));
  EXPECT_EQ(CountToken(toks, "$end"), CountSectionOpeners(toks));
}

// The keyword commands of the file in order: the '$'-introduced tokens, which
// carry the command structure while excluding run-varying data (dates, times,
// values).
std::vector<std::string> KeywordSequence(const std::vector<std::string>& toks) {
  std::vector<std::string> kws;
  for (const auto& t : toks) {
    if (t[0] == '$') kws.push_back(t);
  }
  return kws;
}

// C1's similarity anchor: the head says the extended file is structured like
// the 4-state file of §21.7.2. The same design dumped once through the
// 4-state tasks ($dumpfile/$dumpvars -- the dependency's real syntax) and
// once through $dumpports yields two files whose command structure is the
// same under the free-format projection: identical keyword-command sequences,
// and both satisfy the separation and opener/$end pairing rules.
TEST_F(ExtendedVcdFileFormat, ExtendedFileSharesFourStateCommandStructure) {
  const char* body =
      "  logic a;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    v = 4'b0000;\n"
      "%s"
      "    #10 begin a = 1'b1; v = 4'b1010; end\n"
      "  end\n"
      "endmodule\n";
  auto src = [&](const char* dump_call) {
    char buf[512];
    snprintf(buf, sizeof(buf), body, dump_call);
    return std::string("module t;\n") + buf;
  };
  auto four_state =
      RunVcd(src("    $dumpfile(\"dump1.dump\");\n"
                 "    $dumpvars;\n"));
  auto extended = RunVcd(src("    $dumpports(, \"dump2.dump\");\n"));
  auto toks4 = Tokens(four_state);
  auto tokse = Tokens(extended);
  // Anchor on real dump content so an empty or failed run cannot compare
  // equal vacuously: both files declare both variables and open a checkpoint.
  ASSERT_EQ(CountToken(toks4, "$var"), 2u);
  ASSERT_EQ(CountToken(tokse, "$var"), 2u);
  ASSERT_GE(CountToken(tokse, "$dumpvars"), 1u);
  // Both files obey the shared free-format rules ...
  EXPECT_TRUE(NoFusedCommands(toks4));
  EXPECT_TRUE(NoFusedCommands(tokse));
  EXPECT_EQ(CountToken(toks4, "$end"), CountSectionOpeners(toks4));
  EXPECT_EQ(CountToken(tokse, "$end"), CountSectionOpeners(tokse));
  // ... and their command structures coincide: the ordered keyword commands
  // of the extended file are exactly those of the 4-state file.
  EXPECT_EQ(KeywordSequence(tokse), KeywordSequence(toks4));
}

// C2 over the real-number value command, with the dumped values produced by a
// declaration initializer: the checkpoint records the initializer-given real
// and scalar as separated commands of their own, and a later procedural real
// change joins the file as another white-space-bounded command.
TEST_F(ExtendedVcdFileFormat, RealValueCommandsKeepSeparation) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  real r = 3.5;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 r = 1.25;\n"
      "  end\n"
      "endmodule\n");
  auto lines = Lines(content);
  // a -> '!', r -> '"': both initializer-produced values are rendered as
  // commands on lines of their own in the opening checkpoint ...
  EXPECT_TRUE(HasLine(lines, "0!"));
  EXPECT_TRUE(HasLine(lines, "r3.5 \""));
  // ... and the mid-simulation real change is separated from its timestamp.
  EXPECT_TRUE(HasLine(lines, "#10"));
  EXPECT_TRUE(HasLine(lines, "r1.25 \""));
  EXPECT_TRUE(NoFusedCommands(Tokens(content)));
}

// C3 (readable by a text editor): the white space chosen between commands
// renders the extended dump as ordinary newline-terminated lines of printable
// text -- with the dumped values produced by declaration initializers and the
// later changes exercising the x and z states, every byte is printable ASCII
// or plain white space and the final command is closed by a newline.
TEST_F(ExtendedVcdFileFormat, FileIsPlainLineOrientedText) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  logic [7:0] v = 8'h00;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 v = 8'b10xz01zx;\n"
      "    #10 a = 1'bx;\n"
      "    #10 a = 1'bz;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(content.empty());
  EXPECT_NE(content.find("b10xz01zx \""), std::string::npos);
  EXPECT_NE(content.find("x!"), std::string::npos);
  EXPECT_NE(content.find("z!"), std::string::npos);
  EXPECT_EQ(content.back(), '\n');  // the last command is closed by whitespace
  for (unsigned char c : content) {
    bool text = (c >= 0x20 && c < 0x7F) || c == '\n' || c == '\t' || c == '\r';
    ASSERT_TRUE(text) << "non-text byte 0x" << std::hex << int{c};
  }
}

// Negative: with no writer installed (no dump file in place), the producing
// task is harmless -- the design runs to completion and no file content
// exists for the format rules to apply to.
TEST_F(ExtendedVcdFileFormat, WithoutWriterNoFileContentToFormat) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();  // no VcdWriter installed anywhere
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(ReadVcd().empty());
}

}  // namespace
}  // namespace delta
