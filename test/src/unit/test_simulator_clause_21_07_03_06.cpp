#include <algorithm>
#include <iterator>
#include <set>
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

// §21.7.3.6 (head; its descendant owns the added keyword's own syntax and
// semantics) makes three observable claims about the extended VCD file:
// (1) its general information is presented as a series of sections, each
// bounded by a keyword command and the $end that closes it; (2) keyword
// commands are the means of inserting information into the file -- the dumper
// inserts them itself (a person may also add them by hand, which is outside
// the simulator's reach); (3) the extended format's keyword vocabulary is the
// 4-state vocabulary of §21.7.2.3 plus exactly one additional keyword
// command. All three are runtime rules observable only in the dump file a
// full simulation leaves on disk, so each test drives real source through
// parse, elaboration, lowering, and the scheduler with the driver's
// per-timestep recording loop installed, then inspects the file.
class ExtendedVcdKeywordCommands : public VcdTestBase {
 protected:
  // Runs a single-module source through the full pipeline with the driver's
  // dump loop and returns the dump file contents. `close_file` mirrors the
  // simulation driver's final step of handing the writer the end simulation
  // time as the file is closed; `driver_comment`, when set, has the dumper
  // insert that information into the file after the node information.
  std::string RunVcd(const std::string& src, bool close_file = false,
                     std::string_view driver_comment = {}) {
    SimFixture f;
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    {
      VcdWriter vcd(tmp_path_);
      vcd.WriteHeader("1ns");
      vcd.BeginScope("t");
      // Register in name order so identifier codes are deterministic.
      std::vector<std::pair<std::string_view, Variable*>> vars(
          f.ctx.GetVariables().begin(), f.ctx.GetVariables().end());
      std::sort(vars.begin(), vars.end(),
                [](const auto& a, const auto& b) { return a.first < b.first; });
      for (const auto& [name, var] : vars) {
        vcd.RegisterSignal(name, var->value.width, var);
      }
      vcd.EndScope();
      vcd.EndDefinitions();
      if (!driver_comment.empty()) vcd.WriteComment(driver_comment);
      vcd.ArmDumpvarsStart();
      f.ctx.SetVcdWriter(&vcd);
      f.scheduler.SetPostTimestepCallback([&vcd, &f]() {
        vcd.WriteTimestamp(f.ctx.CurrentTime().ticks);
        vcd.DumpChangedValues(0);
      });
      f.scheduler.Run();
      // The driver's close step: the final simulation time reaches the writer
      // as the file is closed. Only a writer the source's extended dump task
      // marked extended emits anything here.
      if (close_file) vcd.WriteVcdClose(f.ctx.CurrentTime().ticks);
    }  // writer destructor flushes the dump to tmp_path_ before ReadVcd
    return ReadVcd();
  }
};

// The dump file split into its white-space-delimited tokens: the projection
// under which section structure is observable.
std::vector<std::string> Tokens(const std::string& content) {
  std::istringstream iss(content);
  return {std::istream_iterator<std::string>(iss),
          std::istream_iterator<std::string>()};
}

// True when no token fuses a keyword command onto other data: '$' introduces
// a keyword, so after tokenizing on white space it can only start a token.
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

// The distinct keyword commands used in the dump: every '$'-introduced token
// except the $end that closes each section.
std::set<std::string> KeywordCommands(const std::vector<std::string>& toks) {
  std::set<std::string> kws;
  for (const auto& t : toks) {
    if (t[0] == '$' && t != "$end") kws.insert(t);
  }
  return kws;
}

// The keyword-command vocabulary of the 4-state VCD file (§21.7.2.3 declares
// the declaration and simulation keyword commands; each closes with $end).
// The head's claim is measured against this set: the extended file draws on
// it plus exactly one more keyword.
const std::set<std::string>& FourStateKeywords() {
  static const std::set<std::string> kws = {
      "$comment",  "$date",           "$dumpall", "$dumpoff",   "$dumpon",
      "$dumpvars", "$enddefinitions", "$scope",   "$timescale", "$upscope",
      "$var",      "$version"};
  return kws;
}

// The body of the first `keyword` section: the tokens strictly between the
// opening keyword and the next '$'-introduced token. `closed` reports whether
// that next '$' token is the $end bounding the section -- false when the
// section runs into another keyword or the end of the file, so a section
// whose $end went missing is caught rather than matched against a later one.
struct SectionScan {
  std::vector<std::string> body;
  bool closed = false;
};
SectionScan ScanSection(const std::vector<std::string>& toks,
                        std::string_view keyword) {
  SectionScan scan;
  size_t i = 0;
  while (i < toks.size() && toks[i] != keyword) ++i;
  for (++i; i < toks.size(); ++i) {
    if (toks[i][0] == '$') {
      scan.closed = (toks[i] == "$end");
      return scan;
    }
    scan.body.push_back(toks[i]);
  }
  return scan;  // ran off the file: not closed
}

// Keywords the dump uses beyond the 4-state vocabulary.
std::set<std::string> ExtraKeywords(const std::string& content) {
  std::set<std::string> extra;
  for (const auto& kw : KeywordCommands(Tokens(content))) {
    if (FourStateKeywords().count(kw) == 0) extra.insert(kw);
  }
  return extra;
}

const char* kExtendedSrc =
    "module t;\n"
    "  logic a;\n"
    "  initial begin\n"
    "    a = 1'b0;\n"
    "    $dumpports(, \"dump2.dump\");\n"
    "    #10 a = 1'b1;\n"
    "  end\n"
    "endmodule\n";

// General information is presented as keyword-bounded sections: each header
// information section of the extended file opens with its keyword, carries
// its information inside, and closes with an $end -- the date text, the
// writer identification, and the time scale all sit between their section's
// opening keyword and the $end that bounds it.
TEST_F(ExtendedVcdKeywordCommands, GeneralInfoSectionsAreKeywordBounded) {
  auto content = RunVcd(kExtendedSrc);
  auto toks = Tokens(content);
  struct Section {
    const char* keyword;
    const char* info;
  } sections[] = {{"$date", nullptr},  // machine-dependent date text
                  {"$version", "DeltaHDL"},
                  {"$timescale", "1ns"}};
  for (const auto& s : sections) {
    auto scan = ScanSection(toks, s.keyword);
    EXPECT_TRUE(scan.closed) << s.keyword << " section not closed by $end";
    // The section carries its information strictly inside its bounds.
    ASSERT_FALSE(scan.body.empty()) << s.keyword << " section is empty";
    if (s.info != nullptr) {
      EXPECT_NE(std::find(scan.body.begin(), scan.body.end(), s.info),
                scan.body.end())
          << s.info << " escapes its section";
    }
  }
}

// Keyword commands are the dumper's means of inserting information, and not
// only in the header: when the production dumper itself has something to say
// mid-dump -- here the size-limit notice its byte budget triggers -- that
// information enters the extended file as a keyword-bounded comment section
// placed in the value-change region, after the node information closed.
TEST_F(ExtendedVcdKeywordCommands,
       ProductionDumperInsertsInfoAsKeywordSection) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    $dumpportslimit(300);\n"
      "    repeat (40) #1 a = ~a;\n"
      "  end\n"
      "endmodule\n");
  auto p_defs_end = content.find("$enddefinitions");
  ASSERT_NE(p_defs_end, std::string::npos);
  // The inserted section sits in the value-change region, after the node
  // information closed.
  auto p_comment = content.find("$comment", p_defs_end);
  ASSERT_NE(p_comment, std::string::npos) << "no dumper-inserted section";
  // The inserted information sits inside the section -- the section's own
  // $end is the next keyword after the notice text, so nothing leaks out.
  auto toks = Tokens(content);
  auto scan = ScanSection(toks, "$comment");
  EXPECT_TRUE(scan.closed);
  bool notice_inside = false;
  for (const auto& w : scan.body) {
    if (w.find("reached") != std::string::npos) notice_inside = true;
  }
  EXPECT_TRUE(notice_inside);
  EXPECT_TRUE(NoFusedCommands(toks));
}

// The same insertion means serves information originating outside the dump
// engine: text the simulation driver asks the dumper to insert lands in the
// extended file bounded by the comment keyword and its $end -- never as bare
// text floating between sections.
TEST_F(ExtendedVcdKeywordCommands, DriverSuppliedInfoIsKeywordBounded) {
  auto content =
      RunVcd(kExtendedSrc, /*close_file=*/false, "chip revision B2 baseline");
  auto toks = Tokens(content);
  auto scan = ScanSection(toks, "$comment");
  // The inserted text is the section's whole body and the section's own $end
  // is the next keyword after it -- the information cannot float free.
  EXPECT_TRUE(scan.closed);
  EXPECT_EQ(scan.body,
            (std::vector<std::string>{"chip", "revision", "B2", "baseline"}));
  EXPECT_TRUE(NoFusedCommands(toks));
}

// The one addition is a single command, not a pervasive format change: while
// the extended dump is open, everything it writes -- header, node
// information, checkpoint, value changes -- draws only on the inherited
// 4-state keyword vocabulary. The additional keyword enters only at close.
TEST_F(ExtendedVcdKeywordCommands, OpenExtendedFileUsesOnlyInheritedKeywords) {
  auto content = RunVcd(kExtendedSrc, /*close_file=*/false);
  ASSERT_NE(content.find("$enddefinitions"), std::string::npos);
  ASSERT_NE(content.find("#10"), std::string::npos);  // the dump did record
  EXPECT_TRUE(ExtraKeywords(content).empty());
}

// Negative: the additional keyword belongs to the extended format only. A
// 4-state dump -- opened by $dumpfile/$dumpvars rather than the extended
// task -- gains no additional keyword even when the driver runs the same
// close step, so its vocabulary stays within the 4-state set.
TEST_F(ExtendedVcdKeywordCommands, FourStateFileGainsNoAdditionalKeyword) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    $dumpvars;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      /*close_file=*/true);
  ASSERT_NE(content.find("#10"), std::string::npos);  // the dump did record
  EXPECT_TRUE(ExtraKeywords(content).empty());
}

// The extended-ness that admits the one additional keyword follows from the
// extended dump task's execution wherever the source places it: reached from
// an edge-triggered always process instead of an initial block, the closed
// file still shows exactly the single addition over the 4-state vocabulary.
TEST_F(ExtendedVcdKeywordCommands, TaskReachedFromAlwaysStillOneAddition) {
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
      "endmodule\n",
      /*close_file=*/true);
  ASSERT_NE(content.find("#15"), std::string::npos);
  EXPECT_EQ(ExtraKeywords(content).size(), 1u);
  // The full series-of-sections shape survives this variant too.
  auto toks = Tokens(content);
  EXPECT_TRUE(NoFusedCommands(toks));
}

// The head's counting claim measured against the full inherited repertoire:
// a complete extended run -- dump opened by the source's task, driven through
// the inherited checkpoint and control sections ($dumpall, $dumpoff, $dumpon
// reached via the extended control tasks), and closed by the driver -- uses
// exactly one keyword the 4-state vocabulary has no counterpart for, because
// the control commands are inherited rather than additions. The same closed
// file also carries the series-of-sections shape end to end: every keyword
// command that appears opens a section, every section closes, so non-$end
// keyword tokens and $end tokens pair off one to one with nothing fused.
TEST_F(ExtendedVcdKeywordCommands, InheritedControlSectionsAreNotAdditions) {
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
      "endmodule\n",
      /*close_file=*/true);
  auto toks = Tokens(content);
  // The wider inherited vocabulary did reach the file...
  EXPECT_GE(CountToken(toks, "$dumpall"), 1u);
  EXPECT_GE(CountToken(toks, "$dumpoff"), 1u);
  EXPECT_GE(CountToken(toks, "$dumpon"), 1u);
  // ...yet the count of keywords beyond the 4-state set stays at one.
  EXPECT_EQ(ExtraKeywords(content).size(), 1u);
  // Every command in the richer series still opens one $end-closed section.
  EXPECT_TRUE(NoFusedCommands(toks));
  size_t openers = 0;
  size_t ends = 0;
  for (const auto& t : toks) {
    if (t[0] != '$') continue;
    (t == "$end" ? ends : openers)++;
  }
  EXPECT_EQ(openers, ends);
}

// The remaining syntactic position for the task that makes the file
// extended: enabled from a task body rather than an initial or always
// process, the closed file still counts exactly one keyword beyond the
// 4-state vocabulary.
TEST_F(ExtendedVcdKeywordCommands, TaskBodyDumpportsStillOneAddition) {
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
      "endmodule\n",
      /*close_file=*/true);
  ASSERT_NE(content.find("#10"), std::string::npos);
  EXPECT_EQ(ExtraKeywords(content).size(), 1u);
}

// The series-of-sections shape is insensitive to what the value changes
// interleaved between sections look like: with vector, real, and unknown/
// high-impedance scalar changes all recorded between the node information
// and the closing keyword, every keyword still opens one $end-closed
// section and no value-change token masquerades as a keyword command.
TEST_F(ExtendedVcdKeywordCommands, SectionSeriesUnbrokenByAllValueForms) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  logic [7:0] v;\n"
      "  real r;\n"
      "  initial begin\n"
      "    s = 1'b0;\n"
      "    v = 8'b00000000;\n"
      "    r = 0.5;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 v = 8'b10xz01zx;\n"
      "    #10 r = 2.75;\n"
      "    #10 s = 1'bx;\n"
      "    #10 s = 1'bz;\n"
      "  end\n"
      "endmodule\n",
      /*close_file=*/true);
  auto toks = Tokens(content);
  // The value forms did reach the file between the sections (registration is
  // name-ordered, so r -> '!', s -> '"', v -> '#')...
  EXPECT_GE(CountToken(toks, "b10xz01zx"), 1u);
  EXPECT_GE(CountToken(toks, "r2.75"), 1u);
  EXPECT_GE(CountToken(toks, "x\""), 1u);
  EXPECT_GE(CountToken(toks, "z\""), 1u);
  // ...and none of them disturbs the keyword-bounded series.
  EXPECT_TRUE(NoFusedCommands(toks));
  size_t openers = 0;
  size_t ends = 0;
  for (const auto& t : toks) {
    if (t[0] != '$') continue;
    (t == "$end" ? ends : openers)++;
  }
  EXPECT_EQ(openers, ends);
  EXPECT_EQ(ExtraKeywords(content).size(), 1u);
}

}  // namespace
}  // namespace delta
