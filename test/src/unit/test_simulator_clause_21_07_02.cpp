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

// §21.7.2: format of the 4-state VCD file. The subclause's own text (its
// descendants own the file grammar, the value formats, and the keyword
// commands) makes two observable claims about the file as a whole:
// (C1) the dump file is structured as free format -- no command is tied to a
// line or column position, so tokenizing the file on white space alone
// recovers its command structure; (C2) white space separates the commands
// from one another and leaves the file plain line-oriented text a text editor
// can display. Both are runtime rules about the file the dump leaves on disk,
// so each test drives real source (using the dump tasks of §21.7.1.1-§21.7.1.5
// to produce every kind of command) through parse, elaboration, lowering, and
// the scheduler with the driver's per-timestep recording loop installed, then
// inspects the file.
class FourStateVcdFileFormat : public VcdTestBase {
 protected:
  // Runs a single-module source through the full pipeline with the driver's
  // dump loop (timestamp + changed values at the end of each time unit) and
  // returns the dump file contents. The module scope is opened around the
  // variable definitions the way the simulation driver does, so the $scope
  // and $upscope commands are among the commands whose separation is checked.
  std::string RunVcd(const std::string& src) {
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
      // Value change dumping starts once the source's $dumpvars executes.
      vcd.ArmDumpvarsStart();
      f.ctx.SetVcdWriter(&vcd);
      f.scheduler.SetPostTimestepCallback([&vcd, &f]() {
        vcd.WriteTimestamp(f.ctx.CurrentTime().ticks);
        vcd.DumpChangedValues(0);
      });
      f.scheduler.Run();
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
// immediately followed by $dumpall, or a value change flush against $end)
// would leave a token with an interior '$'.
bool NoFusedCommands(const std::vector<std::string>& toks) {
  for (const auto& t : toks) {
    if (t.find('$', 1) != std::string::npos) return false;
  }
  return true;
}

// Occurrences of `tok` as a complete white-space-delimited token.
size_t CountToken(const std::vector<std::string>& toks,
                  std::string_view target) {
  size_t n = 0;
  for (const auto& t : toks) {
    if (t == target) ++n;
  }
  return n;
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

// C2 over the declaration commands: with a scalar, a vector, and a real
// variable dumped, every declaration keyword the header and definitions carry
// ($date, $version, $timescale, $scope, $var, $upscope, $enddefinitions, and
// the $end that closes each section) stands apart as its own white-space
// delimited token, and no token anywhere in the file fuses two commands.
TEST_F(FourStateVcdFileFormat, DeclarationCommandsStandApartAsTokens) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [3:0] v;\n"
      "  real r;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    v = 4'b0000;\n"
      "    r = 3.5;\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    $dumpvars;\n"
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
  // space like the rest: the $dumpvars section renders it on a line of its
  // own (a -> '!', r -> '"', v -> '#').
  EXPECT_TRUE(HasLine(Lines(content), "r3.5 \""));
}

// C2 over the simulation commands: with the dump-control tasks of
// §21.7.1.2-§21.7.1.4 all executed from real source, each simulation keyword
// ($dumpvars, $dumpall, $dumpoff, $dumpon) is a standalone token, every
// simulation-time command is a '#' immediately followed by decimal digits and
// nothing else, and no two commands are ever juxtaposed without white space.
TEST_F(FourStateVcdFileFormat, SimulationCommandsStandApartAsTokens) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpvars;\n"
      "    #10 a = 1'b1;\n"
      "    #10 $dumpall;\n"
      "    #10 $dumpoff;\n"
      "    #10 $dumpon;\n"
      "    #10 a = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  EXPECT_EQ(CountToken(toks, "$dumpvars"), 1u);
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
// change in one time unit, the timestamp and the two value-change commands
// are each separated from their neighbors (rendered one command per line).
// The separation applies BETWEEN commands only -- the scalar change itself
// stays one unsplit token, since its interior belongs to the command.
TEST_F(FourStateVcdFileFormat, ValueChangeCommandsSeparatedFromNeighbors) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    v = 4'b0000;\n"
      "    $dumpvars;\n"
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
// column position discarded -- recovers the command structure. Each
// section-opening keyword is closed by a matching standalone $end token, and
// the single-token commands pair up adjacently ($upscope $end,
// $enddefinitions $end) in the token stream.
TEST_F(FourStateVcdFileFormat, WhitespaceTokenizationRecoversCommandStructure) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpvars;\n"
      "    #10 a = 1'b1;\n"
      "    #10 $dumpall;\n"
      "    #10 $dumpoff;\n"
      "    #10 $dumpon;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  ASSERT_FALSE(toks.empty());
  const char* openers[] = {
      "$date",     "$version", "$timescale", "$scope",
      "$var",      "$upscope", "$comment",   "$enddefinitions",
      "$dumpvars", "$dumpall", "$dumpoff",   "$dumpon"};
  size_t opened = 0;
  for (const char* kw : openers) opened += CountToken(toks, kw);
  EXPECT_EQ(CountToken(toks, "$end"), opened);
  for (size_t i = 0; i + 1 < toks.size(); ++i) {
    if (toks[i] == "$upscope" || toks[i] == "$enddefinitions") {
      EXPECT_EQ(toks[i + 1], "$end") << "after " << toks[i];
    }
  }
}

// C2 over a dumper-inserted command: the $comment section the dumper itself
// inserts when the §21.7.1.5 size limit is reached joins the file as a
// white-space-separated command like any other -- $comment and its closing
// $end are standalone tokens and the opener/$end pairing still balances.
TEST_F(FourStateVcdFileFormat, DumperInsertedCommentIsSeparatedCommand) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'h11;\n"
      "    #10 $dumplimit(1);\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  EXPECT_EQ(CountToken(toks, "$comment"), 1u);
  EXPECT_TRUE(NoFusedCommands(toks));
  const char* openers[] = {
      "$date",     "$version", "$timescale", "$scope",
      "$var",      "$upscope", "$comment",   "$enddefinitions",
      "$dumpvars", "$dumpall", "$dumpoff",   "$dumpon"};
  size_t opened = 0;
  for (const char* kw : openers) opened += CountToken(toks, kw);
  EXPECT_EQ(CountToken(toks, "$end"), opened);
}

// The producing tasks are ordinary task enables: moved into a task body, the
// same run yields a file with the same separation properties -- the command
// text depends on what was dumped, not on the syntactic position of the tasks
// that produced it.
TEST_F(FourStateVcdFileFormat, TaskBodyProducedCommandsKeepSeparation) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  task start_dump;\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    $dumpvars;\n"
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

// C3 (readable by a text editor): the white space chosen between commands
// renders the dump as ordinary newline-terminated lines of printable text --
// every byte is printable ASCII or plain white space, the final command is
// closed by a newline, and every non-empty line holds visible text.
TEST_F(FourStateVcdFileFormat, FileIsPlainLineOrientedText) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    v = 8'h00;\n"
      "    $dumpvars;\n"
      "    #10 v = 8'b10xz01zx;\n"
      "    #10 a = 1'bx;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(content.empty());
  EXPECT_EQ(content.back(), '\n');  // the last command is closed by whitespace
  for (unsigned char c : content) {
    bool text = (c >= 0x20 && c < 0x7F) || c == '\n' || c == '\t' || c == '\r';
    ASSERT_TRUE(text) << "non-text byte 0x" << std::hex << int{c};
  }
}

// Negative: with no writer installed (no dump file in place), the producing
// tasks are harmless -- the design runs to completion and no file content
// exists for the format rules to apply to.
TEST_F(FourStateVcdFileFormat, WithoutWriterNoFileContentToFormat) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    $dumpvars;\n"
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
