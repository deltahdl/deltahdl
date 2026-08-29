// $sdf_annotate as it is actually written: a call in the design's source.
//
// What each operand does depends on how the call was written and on what the
// design already holds, so these cases build the SystemVerilog side from real
// source -- parsed, elaborated, lowered and run -- put the SDF and
// configuration files they name on disk as real files, and let the calls the
// source writes drive the annotation. Most of them turn on §32.9's
// module_instance operand and on which cells of a file it admits: a cell at the
// level it names, one above that level, one in a sibling level, one whose path
// merely begins with the same text, and one element of an instance array.
//
// Every cell an SDF file here names is a module instance the design really
// declares, and the module path a cell's IOPATH annotates is declared in that
// instance's own module. §30.3 puts a specify block inside a module
// declaration, so a cell's timing belongs to the cell rather than to whatever
// instantiates it, and each case reads the annotated delay back under the
// hierarchical prefix of the instance its SDF named.
//
// The manager read back is the one the run installed. Lowerer::Lower acquires
// it through SimContext::AcquireSpecifyManager and registers every instance's
// specify block under that instance's prefix, so a path declared inside
// instance `a` stands there under "a.". A case that binds a manager of its own
// through SimContext::SetSpecifyManager discards all of that and reads back a
// manager holding the top module's paths alone under an empty prefix, which is
// what let a cell naming a child instance appear to annotate a path the child
// had never declared.
//
// The literals are picked so that no two quantities a case tells apart share a
// value. Every cell declares its module path at 7; no SDF file here writes 7
// and no scaling here produces it, so a path nothing annotated is told from
// every annotated value. DelayIn answers kNoPath rather than 0 for a path the
// manager does not hold, so a design that registered nothing is not read as an
// annotation that did not land.
//
// No module here is named `cell`. §33.4 gives that keyword to a config
// declaration's cell clause, and the parser rejects it as a module name.
//
// The other half of §32.9 is in test_simulator_subclause_32_09a.cpp, which
// calls the SDF reader and the scaling directly. The two files were one until
// #3157, which split it at 997 lines, 3 short of the maximum
// assert-no-oversized-source-files enforces.

#include <gtest/gtest.h>

#include <cstdint>
#include <cstdio>
#include <fstream>
#include <ios>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_sdf_design.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

// The delay every cell below declares for its module path, and so the delay a
// path an annotation did not reach still holds.
constexpr uint64_t kDeclaredDelay = 7;

// What DelayIn answers when the manager holds no such path at all. It is
// distinct from every delay a case expects, so a design that never registered
// its path fails rather than reading as a path an annotation missed.
constexpr uint64_t kNoPath = UINT64_MAX;

// Lowers and runs `src`, so the $sdf_annotate call the source writes is what
// annotates. False when the source did not lower, which every case asserts on
// before reading anything back. Nothing is bound to the context here:
// Lowerer::Lower installs the manager and registers the design's specify blocks
// into it, and that is the manager DelayIn and AnnotationCount read.
bool BuildAndRun(SdfDesign& d, const std::string& src) {
  if (!d.Lower(src)) return false;
  d.f.scheduler.Run();
  return true;
}

// The delay standing on the module path of the instance whose hierarchical
// prefix is `prefix`: "" for a path the top module itself declared, "a." for
// one declared by the module instantiated as `a`, "bank[1].c." for one
// declared two levels down. Every module path in this file runs from port A to
// port Z, exactly as two instances of one cell do, so the prefix is the only
// thing that separates one instance's path from another's and
// SpecifyManager::GetPathDelay, which selects on the port pair alone, cannot
// answer for either.
uint64_t DelayIn(SdfDesign& d, std::string_view prefix) {
  SpecifyManager* mgr = d.f.ctx.GetSpecifyManager();
  if (mgr == nullptr) return kNoPath;
  for (const auto& pd : mgr->GetPathDelays()) {
    if (pd.inst_prefix == prefix && pd.src_port == "A" && pd.dst_port == "Z") {
      return pd.delays[0];
    }
  }
  return kNoPath;
}

// How many annotations of the design the run recorded. §32.6 makes each call
// one annotation, recorded whether or not the file it named turned out to be
// readable.
std::size_t AnnotationCount(SdfDesign& d) {
  SpecifyManager* mgr = d.f.ctx.GetSpecifyManager();
  return mgr == nullptr ? 0 : mgr->GetSdfAnnotations().size();
}

// The number of non-empty lines `path` holds, which is how many entries a log
// file the annotator wrote carries. A file the annotator never wrote holds
// none, and no case expects none, so a log that was not written fails the case
// that asked for one.
std::size_t LogEntryCount(const std::string& path) {
  std::ifstream in(path);
  std::size_t lines = 0;
  std::string line;
  while (std::getline(in, line)) {
    if (!line.empty()) ++lines;
  }
  return lines;
}

std::string WriteTempFile(const std::string& name, const std::string& text) {
  const std::string kPath = std::string("/tmp/delta_c32_09_") + name;
  std::ofstream out(kPath, std::ios::trunc);
  out << text;
  out.close();
  return kPath;
}

// The cell an SDF CELL record names: one module path from A to Z, declared in
// the module the design instantiates. Lowerer::Lower registers this block once
// per instance of the module, each under its own prefix, which is what gives
// each instance a path of its own for an IOPATH to reach.
std::string CellDecl(const std::string& name) {
  return "module " + name +
         "(input A, output Z);\n"
         "  specify\n"
         "    (A => Z) = " +
         std::to_string(kDeclaredDelay) +
         ";\n"
         "  endspecify\n"
         "endmodule\n";
}

// One CELL record naming instance path `instance`, with a single IOPATH from A
// to Z carrying `delay` -- a plain number or a min:typ:max triple.
std::string CellRecord(const std::string& instance, const std::string& delay) {
  return " (CELL (CELLTYPE \"timed_cell\") (INSTANCE " + instance +
         ") (DELAY (ABSOLUTE (IOPATH A Z (" + delay + ")))))";
}

std::string DelayFile(const std::string& cells) {
  return "(DELAYFILE" + cells + ")";
}

// A cell whose single module path carries three distinct min:typ:max values, so
// the annotated delay reveals which triple member and which scaling the call's
// operands selected.
std::string TripleSdf() { return DelayFile(CellRecord("top/a", "1:2:3")); }

// The design most cases annotate: the cell, one instance `a` of it for a CELL
// record to name, whatever `decls` the case adds among the module items, and
// `body` as the statement the initial block runs.
std::string OneCellSource(const std::string& decls, const std::string& body) {
  return CellDecl("timed_cell") +
         "module top;\n"
         "  wire src;\n"
         "  wire dst;\n"
         "  timed_cell a(src, dst);\n" +
         decls + "  initial " + body + "\n" + "endmodule\n";
}

// The same design where the call is all the initial block does and the test
// supplies only its operand list.
std::string OneCellDesign(const std::string& call_args) {
  return OneCellSource("", "$sdf_annotate(" + call_args + ");");
}

// A design instantiating one cell twice. The two instances declare paths
// carrying identical port names and differing in nothing but the instance that
// declared them, so which instance an annotation reached shows in the prefix
// alone.
std::string TwoCellDesign(const std::string& call_args) {
  return CellDecl("timed_cell") +
         "module top;\n"
         "  wire src;\n"
         "  wire out_a;\n"
         "  wire out_b;\n"
         "  timed_cell a(src, out_a);\n"
         "  timed_cell b(src, out_b);\n"
         "  initial $sdf_annotate(" +
         call_args +
         ");\n"
         "endmodule\n";
}

// A design whose cell is instantiated as an instance array. §23.3.3.5 makes
// each element an instance of its own, named `bank[0]` and `bank[1]`, so each
// declares its own copy of the cell's module path.
std::string BankDesign(const std::string& decls, const std::string& call_args) {
  return CellDecl("timed_cell") +
         "module top;\n"
         "  wire [1:0] ins;\n"
         "  wire [1:0] outs;\n"
         "  timed_cell bank[1:0](ins, outs);\n" +
         decls + "  initial $sdf_annotate(" + call_args +
         ");\n"
         "endmodule\n";
}

// Runs one call over the shared triple-valued SDF file and reports the delay
// instance `a`'s module path ended up holding.
uint64_t AnnotatedTripleDelay(const std::string& file_name,
                              const std::string& trailing_args) {
  const std::string kSdf = WriteTempFile(file_name, TripleSdf());
  SdfDesign d;
  EXPECT_TRUE(
      BuildAndRun(d, OneCellDesign("\"" + kSdf + "\"" + trailing_args)));
  return DelayIn(d, "a.");
}

// The sdf_file operand as a string literal: the plainest way to name the file
// to be opened.
TEST(SdfAnnotateTask, StringLiteralOperandNamesTheFileToRead) {
  const std::string kSdf =
      WriteTempFile("literal.sdf", DelayFile(CellRecord("top/a", "17")));
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, OneCellDesign("\"" + kSdf + "\"")));
  EXPECT_EQ(DelayIn(d, "a."), 17u);
}

// sdf_file is an expression, so a `string` variable holding the name works the
// same way a literal does.
TEST(SdfAnnotateTask, StringVariableOperandNamesTheFileToRead) {
  const std::string kSdf =
      WriteTempFile("strvar.sdf", DelayFile(CellRecord("top/a", "18")));
  SdfDesign d;
  ASSERT_TRUE(
      BuildAndRun(d, OneCellSource("  string fname = \"" + kSdf + "\";\n",
                                   "$sdf_annotate(fname);")));
  EXPECT_EQ(DelayIn(d, "a."), 18u);
}

// An integral variable whose bytes spell the file name is the third form the
// sdf_file operand admits.
TEST(SdfAnnotateTask, IntegralVariableOperandNamesTheFileToRead) {
  const std::string kSdf =
      WriteTempFile("intvar.sdf", DelayFile(CellRecord("top/a", "19")));
  SdfDesign d;
  ASSERT_TRUE(
      BuildAndRun(d, OneCellSource("  reg [8*" + std::to_string(kSdf.size()) +
                                       ":1] fname = \"" + kSdf + "\";\n",
                                   "$sdf_annotate(fname);")));
  EXPECT_EQ(DelayIn(d, "a."), 19u);
}

// The operand is an expression read when the call runs, so a variable that only
// takes the file name in an earlier statement of the same block still names the
// file the call opens.
TEST(SdfAnnotateTask, SdfFileOperandIsReadWhereTheCallRuns) {
  const std::string kSdf =
      WriteTempFile("assigned.sdf", DelayFile(CellRecord("top/a", "23")));
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(
      d, OneCellSource("  string fname;\n",
                       "begin\n    fname = \"" + kSdf +
                           "\";\n    $sdf_annotate(fname);\n  end")));
  EXPECT_EQ(DelayIn(d, "a."), 23u);
}

// sdf_file is the one operand a call cannot leave out: with no file named there
// is nothing to read, which is reported rather than passed over.
TEST(SdfAnnotateTask, CallWithNoSdfFileOperandIsReportedAndAnnotatesNothing) {
  const std::string kSrc = OneCellDesign("");
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, kSrc));
  EXPECT_TRUE(ReportedError(d.f.diag.Diagnostics(),
                            "$sdf_annotate requires an SDF file name",
                            LineHolding(kSrc, "$sdf_annotate"), "32.9"));
  EXPECT_EQ(DelayIn(d, "a."), kDeclaredDelay);
  EXPECT_EQ(AnnotationCount(d), 0u);
}

// The same holds when the call reaches past an empty first slot to a later
// operand: it still names no file, so there is nothing to read.
TEST(SdfAnnotateTask, CallWithAnEmptySdfFileSlotIsReportedAndAnnotatesNothing) {
  const std::string kSrc = OneCellDesign(", top.a");
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, kSrc));
  EXPECT_TRUE(ReportedError(d.f.diag.Diagnostics(),
                            "$sdf_annotate requires an SDF file name",
                            LineHolding(kSrc, "$sdf_annotate"), "32.9"));
  EXPECT_EQ(DelayIn(d, "a."), kDeclaredDelay);
  EXPECT_EQ(AnnotationCount(d), 0u);
}

// A file that cannot be opened carries no timing data, so the design keeps what
// it already held and the call is reported.
TEST(SdfAnnotateTask, UnreadableSdfFileIsReportedAndLeavesTheDesignAlone) {
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(
      d, OneCellDesign("\"/tmp/delta_c32_09_absent_dir/none.sdf\"")));
  EXPECT_EQ(DelayIn(d, "a."), kDeclaredDelay);
  EXPECT_GT(d.f.diag.WarningCount(), 0u);

  // The call still counts as an annotation of the design having been asked for.
  EXPECT_EQ(AnnotationCount(d), 1u);
}

// module_instance names the hierarchy level the annotator works from, so a cell
// outside that level is not annotated. Both instances declare the same module
// path, so the cell that was left out is one whose path is still standing at
// the delay its cell declared.
TEST(SdfAnnotateTask, ModuleInstanceOperandSelectsTheHierarchyLevelAnnotated) {
  const std::string kSdf = WriteTempFile(
      "scope.sdf",
      DelayFile(CellRecord("top/a", "10") + CellRecord("top/b", "20")));
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, TwoCellDesign("\"" + kSdf + "\", top.a")));
  EXPECT_EQ(DelayIn(d, "a."), 10u);
  EXPECT_EQ(DelayIn(d, "b."), kDeclaredDelay);
}

// Array indices are permitted in a module_instance, so one element of an
// instance array is a hierarchy level of its own.
TEST(SdfAnnotateTask, ModuleInstanceOperandMayCarryArrayIndices) {
  const std::string kSdf =
      WriteTempFile("indexed.sdf", DelayFile(CellRecord("top/bank[0]", "10") +
                                             CellRecord("top/bank[1]", "20")));
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, BankDesign("", "\"" + kSdf + "\", top.bank[1]")));
  EXPECT_EQ(DelayIn(d, "bank[0]."), kDeclaredDelay);
  EXPECT_EQ(DelayIn(d, "bank[1]."), 20u);
}

// An index is an expression, so an element may be picked out by a constant the
// design declares rather than by a plain number written in the call.
TEST(SdfAnnotateTask, ModuleInstanceIndexMayBeWrittenAsADeclaredConstant) {
  const std::string kSdf = WriteTempFile(
      "indexed_param.sdf", DelayFile(CellRecord("top/bank[0]", "10") +
                                     CellRecord("top/bank[1]", "20")));
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, BankDesign("  localparam int SEL = 1;\n",
                                        "\"" + kSdf + "\", top.bank[SEL]")));
  EXPECT_EQ(DelayIn(d, "bank[0]."), kDeclaredDelay);
  EXPECT_EQ(DelayIn(d, "bank[1]."), 20u);
}

// An index part way along a hierarchical path is an ordinary module_instance
// too: the level named here sits below an indexed instance.
TEST(SdfAnnotateTask, ModuleInstanceMayIndexPartWayAlongAPath) {
  const std::string kSdf = WriteTempFile(
      "indexed_deep.sdf", DelayFile(CellRecord("top/bank[0]/c", "10") +
                                    CellRecord("top/bank[1]/c", "26")));
  const std::string kSrc = CellDecl("timed_cell") +
                           "module blk(input A, output Z);\n"
                           "  timed_cell c(A, Z);\n"
                           "endmodule\n"
                           "module top;\n"
                           "  wire [1:0] ins;\n"
                           "  wire [1:0] outs;\n"
                           "  blk bank[1:0](ins, outs);\n"
                           "  initial $sdf_annotate(\"" +
                           kSdf +
                           "\", top.bank[1].c);\n"
                           "endmodule\n";

  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, kSrc));
  EXPECT_EQ(DelayIn(d, "bank[0].c."), kDeclaredDelay);
  EXPECT_EQ(DelayIn(d, "bank[1].c."), 26u);
}

// A module_instance may be a bare instance name rather than a dotted path, in
// which case it names that instance's level directly.
TEST(SdfAnnotateTask, ModuleInstanceMayBeABareInstanceName) {
  const std::string kSdf = WriteTempFile(
      "bare.sdf", DelayFile(CellRecord("a", "24") + CellRecord("b", "25")));
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, TwoCellDesign("\"" + kSdf + "\", a")));
  EXPECT_EQ(DelayIn(d, "a."), 24u);
  EXPECT_EQ(DelayIn(d, "b."), kDeclaredDelay);
}

// A module_instance names a level of the hierarchy, not a run of characters:
// a cell whose path merely starts with the same text is at a different level
// and is left alone, and so is a cell sitting above the named level. The third
// cell here really is inside the named level, so the file is demonstrably being
// read and it is the level test that keeps the other two out.
TEST(SdfAnnotateTask, ModuleInstanceSelectsAHierarchyLevelNotATextualPrefix) {
  const std::string kSdf = WriteTempFile(
      "level.sdf", DelayFile(CellRecord("top/ax", "10") +
                             " (CELL (CELLTYPE \"top\") (INSTANCE top)"
                             " (DELAY (ABSOLUTE (IOPATH A Z (20)))))" +
                             CellRecord("top/a/deep", "30")));
  const std::string kSrc = CellDecl("timed_cell") +
                           "module blk(input A, output Z);\n"
                           "  timed_cell deep(A, Z);\n"
                           "endmodule\n"
                           "module top(input A, output Z);\n"
                           "  wire out_ax;\n"
                           "  blk a(A, Z);\n"
                           "  timed_cell ax(A, out_ax);\n"
                           "  specify\n"
                           "    (A => Z) = " +
                           std::to_string(kDeclaredDelay) +
                           ";\n"
                           "  endspecify\n"
                           "  initial $sdf_annotate(\"" +
                           kSdf +
                           "\", top.a);\n"
                           "endmodule\n";

  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, kSrc));
  EXPECT_EQ(DelayIn(d, "ax."), kDeclaredDelay);
  EXPECT_EQ(DelayIn(d, ""), kDeclaredDelay);
  EXPECT_EQ(DelayIn(d, "a.deep."), 30u);
}

// With module_instance left out, the annotator works from the module that holds
// the call, so a cell outside that module's hierarchy is not annotated.
TEST(SdfAnnotateTask, OmittedModuleInstanceUsesTheModuleHoldingTheCall) {
  const std::string kSdf = WriteTempFile(
      "default_scope.sdf",
      DelayFile(CellRecord("top/a", "10") + CellRecord("elsewhere/b", "20")));
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, TwoCellDesign("\"" + kSdf + "\"")));
  EXPECT_EQ(DelayIn(d, "a."), 10u);
  EXPECT_EQ(DelayIn(d, "b."), kDeclaredDelay);
}

// Table 32-5: each mtm_spec keyword annotates its own member of the min:typ:max
// triple. The keyword sits after three operands the call has no use for, so the
// call skips over them to reach it.
TEST(SdfAnnotateTask, MtmSpecOperandSelectsTheTripleMemberAnnotated) {
  EXPECT_EQ(AnnotatedTripleDelay("mtm_min.sdf", ", , , , \"MINIMUM\""), 1u);
  EXPECT_EQ(AnnotatedTripleDelay("mtm_typ.sdf", ", , , , \"TYPICAL\""), 2u);
  EXPECT_EQ(AnnotatedTripleDelay("mtm_max.sdf", ", , , , \"MAXIMUM\""), 3u);
}

// Table 32-5: TOOL_CONTROL leaves the choice to the simulator, and is what a
// call that names no mtm_spec at all gets.
TEST(SdfAnnotateTask, ToolControlIsTheMtmSpecDefault) {
  const uint64_t kExplicit =
      AnnotatedTripleDelay("mtm_tool.sdf", ", , , , \"TOOL_CONTROL\"");
  const uint64_t kOmitted = AnnotatedTripleDelay("mtm_none.sdf", "");
  EXPECT_EQ(kExplicit, kOmitted);
}

// An mtm_spec that is not one of the Table 32-5 keywords is reported rather
// than quietly taken as the default.
TEST(SdfAnnotateTask, UnknownMtmSpecKeywordIsReported) {
  const std::string kSdf = WriteTempFile("mtm_bogus.sdf", TripleSdf());
  SdfDesign d;
  ASSERT_TRUE(
      BuildAndRun(d, OneCellDesign("\"" + kSdf + "\", , , , \"MOSTLY\"")));
  EXPECT_GT(d.f.diag.WarningCount(), 0u);
}

// The multipliers default to one apiece, so a call naming no scale_factors
// annotates the values the file wrote, and naming the identity triple is the
// same as naming nothing. (What each factor multiplies is the next test.)
TEST(SdfAnnotateTask, DefaultScaleFactorsLeaveTheAnnotatedValuesAsWritten) {
  EXPECT_EQ(AnnotatedTripleDelay("sf_none.sdf", ", , , , \"MAXIMUM\""), 3u);
  EXPECT_EQ(AnnotatedTripleDelay("sf_unit.sdf",
                                 ", , , , \"MAXIMUM\", \"1.0:1.0:1.0\""),
            3u);
}

// The three factors are positional: the first multiplies the minimum member of
// each triple, the second the typical one and the third the maximum one. A
// triple of 10:20:30 under factors of 1.6, 1.4 and 1.2 makes all three readings
// land on distinct whole numbers, so each factor is seen on its own member.
TEST(SdfAnnotateTask, EachScaleFactorMultipliesItsOwnTripleMember) {
  const std::string kSdf = WriteTempFile(
      "sf_positional.sdf", DelayFile(CellRecord("top/a", "10:20:30")));

  auto under = [&](const std::string& mtm) {
    SdfDesign d;
    EXPECT_TRUE(BuildAndRun(d, OneCellDesign("\"" + kSdf + "\", , , , \"" +
                                             mtm + "\", \"1.6:1.4:1.2\"")));
    return DelayIn(d, "a.");
  };

  EXPECT_EQ(under("MINIMUM"), 16u);
  EXPECT_EQ(under("TYPICAL"), 28u);
  EXPECT_EQ(under("MAXIMUM"), 36u);
}

// Table 32-6: scale_type decides which member of the triple each factor is
// applied to. Reading the result at both ends of the triple tells all four
// keywords apart.
TEST(SdfAnnotateTask, ScaleTypeOperandSelectsWhatTheFactorsAreAppliedTo) {
  auto pair = [](const std::string& tag, const std::string& scale_type) {
    const std::string kMinArgs =
        ", , , , \"MINIMUM\", \"2.0:3.0:4.0\", \"" + scale_type + "\"";
    const std::string kMaxArgs =
        ", , , , \"MAXIMUM\", \"2.0:3.0:4.0\", \"" + scale_type + "\"";
    return std::pair<uint64_t, uint64_t>{
        AnnotatedTripleDelay(tag + "_lo.sdf", kMinArgs),
        AnnotatedTripleDelay(tag + "_hi.sdf", kMaxArgs)};
  };

  EXPECT_EQ(pair("st_mtm", "FROM_MTM"), (std::pair<uint64_t, uint64_t>{2, 12}));
  EXPECT_EQ(pair("st_min", "FROM_MINIMUM"),
            (std::pair<uint64_t, uint64_t>{2, 4}));
  EXPECT_EQ(pair("st_typ", "FROM_TYPICAL"),
            (std::pair<uint64_t, uint64_t>{4, 8}));
  EXPECT_EQ(pair("st_max", "FROM_MAXIMUM"),
            (std::pair<uint64_t, uint64_t>{6, 12}));
}

// Table 32-6: FROM_MTM is the default, so a call that names no scale_type
// behaves as one that names FROM_MTM.
TEST(SdfAnnotateTask, FromMtmIsTheScaleTypeDefault) {
  const uint64_t kExplicit = AnnotatedTripleDelay(
      "st_default_explicit.sdf",
      ", , , , \"MAXIMUM\", \"2.0:3.0:4.0\", \"FROM_MTM\"");
  const uint64_t kOmitted = AnnotatedTripleDelay(
      "st_default_omitted.sdf", ", , , , \"MAXIMUM\", \"2.0:3.0:4.0\"");
  EXPECT_EQ(kExplicit, kOmitted);
  EXPECT_EQ(kExplicit, 12u);
}

// A scale_type that is not one of the Table 32-6 keywords is reported.
TEST(SdfAnnotateTask, UnknownScaleTypeKeywordIsReported) {
  const std::string kSdf = WriteTempFile("st_bogus.sdf", TripleSdf());
  SdfDesign d;
  ASSERT_TRUE(
      BuildAndRun(d, OneCellDesign("\"" + kSdf +
                                   "\", , , , \"MAXIMUM\", \"1.0:1.0:1.0\", "
                                   "\"FROM_NOWHERE\"")));
  EXPECT_GT(d.f.diag.WarningCount(), 0u);
}

// The configuration file controls the same aspects of annotation the call's own
// operands do, so a call naming only a configuration file is annotated under
// that file's keywords.
TEST(SdfAnnotateTask, ConfigFileKeywordsControlTheAnnotation) {
  const std::string kCfg = WriteTempFile("cfg_mtm.txt",
                                         "// annotation settings\n"
                                         "MTM_SPEC MAXIMUM;\n");
  EXPECT_EQ(AnnotatedTripleDelay("cfg_mtm.sdf", ", , \"" + kCfg + "\""), 3u);

  const std::string kCfgFactors =
      WriteTempFile("cfg_factors.txt", "SCALE_FACTORS 2.0:3.0:4.0;\n");
  EXPECT_EQ(AnnotatedTripleDelay("cfg_factors.sdf",
                                 ", , \"" + kCfgFactors + "\", , \"MAXIMUM\""),
            12u);

  const std::string kCfgType = WriteTempFile("cfg_type.txt",
                                             "SCALE_FACTORS 2.0:3.0:4.0;\n"
                                             "SCALE_TYPE FROM_MINIMUM;\n");
  EXPECT_EQ(AnnotatedTripleDelay("cfg_type.sdf",
                                 ", , \"" + kCfgType + "\", , \"MAXIMUM\""),
            4u);
}

// An mtm_spec written on the call overrides the configuration file's MTM_SPEC.
TEST(SdfAnnotateTask, MtmSpecOperandOverridesTheConfigFileKeyword) {
  const std::string kCfg = WriteTempFile("ovr_mtm.txt", "MTM_SPEC MAXIMUM;\n");
  EXPECT_EQ(AnnotatedTripleDelay("ovr_mtm.sdf",
                                 ", , \"" + kCfg + "\", , \"MINIMUM\""),
            1u);
}

// scale_factors written on the call overrides the configuration file's
// SCALE_FACTORS.
TEST(SdfAnnotateTask, ScaleFactorsOperandOverridesTheConfigFileKeyword) {
  const std::string kCfg =
      WriteTempFile("ovr_factors.txt", "SCALE_FACTORS 2.0:2.0:2.0;\n");
  EXPECT_EQ(AnnotatedTripleDelay(
                "ovr_factors.sdf",
                ", , \"" + kCfg + "\", , \"MAXIMUM\", \"3.0:3.0:3.0\""),
            9u);
}

// scale_type written on the call overrides the configuration file's SCALE_TYPE.
TEST(SdfAnnotateTask, ScaleTypeOperandOverridesTheConfigFileKeyword) {
  const std::string kCfg =
      WriteTempFile("ovr_type.txt", "SCALE_TYPE FROM_MAXIMUM;\n");
  EXPECT_EQ(AnnotatedTripleDelay("ovr_type.sdf",
                                 ", , \"" + kCfg +
                                     "\", , \"MAXIMUM\", \"1.0:1.0:1.0\", "
                                     "\"FROM_MINIMUM\""),
            1u);
}

// A configuration file that cannot be opened is reported; the annotation still
// runs under whatever the call itself supplied.
TEST(SdfAnnotateTask, UnreadableConfigFileIsReported) {
  const std::string kSdf = WriteTempFile("cfg_absent.sdf", TripleSdf());
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(
      d, OneCellDesign("\"" + kSdf +
                       "\", , \"/tmp/delta_c32_09_absent_dir/cfg.txt\"")));
  EXPECT_GT(d.f.diag.WarningCount(), 0u);
  EXPECT_EQ(DelayIn(d, "a."), 2u);
}

// The configuration file is named by an ordinary character-string operand, so a
// variable holding the name works the same way a literal does.
TEST(SdfAnnotateTask, ConfigFileMayBeNamedByAStringVariable) {
  const std::string kSdf = WriteTempFile("cfg_var.sdf", TripleSdf());
  const std::string kCfg = WriteTempFile("cfg_var.txt", "MTM_SPEC MAXIMUM;\n");
  SdfDesign d;
  ASSERT_TRUE(
      BuildAndRun(d, OneCellSource("  string cfg = \"" + kCfg + "\";\n",
                                   "$sdf_annotate(\"" + kSdf + "\", , cfg);")));
  EXPECT_EQ(DelayIn(d, "a."), 3u);
}

// A log file that cannot be written is reported, and the annotation the call
// asked for still lands.
TEST(SdfAnnotateTask, UnwritableLogFileIsReported) {
  const std::string kSdf =
      WriteTempFile("log_absent.sdf", DelayFile(CellRecord("top/a", "28")));
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(
      d, OneCellDesign("\"" + kSdf +
                       "\", , , \"/tmp/delta_c32_09_absent_dir/run.log\"")));
  EXPECT_EQ(DelayIn(d, "a."), 28u);
  EXPECT_GT(d.f.diag.WarningCount(), 0u);
}

// With a log_file named, each individual annotation the SDF file carries earns
// its own entry in it.
TEST(SdfAnnotateTask, LogFileOperandRecordsAnEntryPerIndividualAnnotation) {
  const std::string kSdf =
      WriteTempFile("logged.sdf",
                    "(DELAYFILE (CELL (CELLTYPE \"timed_cell\") (INSTANCE "
                    "top/a) (DELAY (ABSOLUTE"
                    " (IOPATH A Z (10))"
                    " (IOPATH B Z (11))"
                    " (IOPATH C Z (12))))))");
  const std::string kLog = std::string("/tmp/delta_c32_09_run.log");
  std::remove(kLog.c_str());

  SdfDesign d;
  ASSERT_TRUE(
      BuildAndRun(d, OneCellDesign("\"" + kSdf + "\", , , \"" + kLog + "\"")));

  EXPECT_EQ(LogEntryCount(kLog), 3u);
  std::remove(kLog.c_str());
}

// The log records the annotations a call actually made, so a call aimed at one
// region leaves out the entries for cells that region does not cover.
TEST(SdfAnnotateTask, LogFileRecordsOnlyAnnotationsInsideTheNamedRegion) {
  const std::string kSdf = WriteTempFile(
      "logged_scoped.sdf",
      DelayFile(CellRecord("top/a", "10") + CellRecord("top/b", "20")));
  const std::string kLog = std::string("/tmp/delta_c32_09_scoped.log");
  std::remove(kLog.c_str());

  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(
      d, TwoCellDesign("\"" + kSdf + "\", top.a, , \"" + kLog + "\"")));

  // Only the cell inside the named region was annotated.
  EXPECT_EQ(DelayIn(d, "a."), 10u);
  EXPECT_EQ(DelayIn(d, "b."), kDeclaredDelay);

  std::ifstream in(kLog);
  ASSERT_TRUE(in.is_open());
  std::stringstream contents;
  contents << in.rdbuf();
  const std::string kText = contents.str();
  EXPECT_NE(kText.find("top/a"), std::string::npos);
  EXPECT_EQ(kText.find("top/b"), std::string::npos);
  std::remove(kLog.c_str());
}

// log_file is optional; a call that names none annotates the design without
// writing a log anywhere.
TEST(SdfAnnotateTask, OmittedLogFileWritesNoLog) {
  const std::string kSdf =
      WriteTempFile("unlogged.sdf", DelayFile(CellRecord("top/a", "14")));
  const std::string kLog = std::string("/tmp/delta_c32_09_unwritten.log");
  std::remove(kLog.c_str());

  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, OneCellDesign("\"" + kSdf + "\"")));

  EXPECT_EQ(DelayIn(d, "a."), 14u);
  std::ifstream in(kLog);
  EXPECT_FALSE(in.is_open());
}

// §32.6 annotates more than one SDF file in turn; when two calls name one log
// file, the entries of both are in it rather than the later call's alone.
TEST(SdfAnnotateTask, TwoCallsNamingOneLogFileBothContributeEntries) {
  const std::string kSdf1 =
      WriteTempFile("logged_a.sdf",
                    "(DELAYFILE (CELL (CELLTYPE \"timed_cell\") (INSTANCE "
                    "top/a) (DELAY (ABSOLUTE (IOPATH A Z (10))"
                    " (IOPATH B Z (11))))))");
  const std::string kSdf2 =
      WriteTempFile("logged_b.sdf", DelayFile(CellRecord("top/a", "12")));
  const std::string kLog = std::string("/tmp/delta_c32_09_two_calls.log");
  std::remove(kLog.c_str());

  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(
      d,
      OneCellSource("", "begin\n    $sdf_annotate(\"" + kSdf1 + "\", , , \"" +
                            kLog + "\");\n    $sdf_annotate(\"" + kSdf2 +
                            "\", , , \"" + kLog + "\");\n  end")));

  EXPECT_EQ(LogEntryCount(kLog), 3u);
  std::remove(kLog.c_str());
}

// A configuration file may write its keywords with an '=' between keyword and
// value, quote the value, and carry comment lines; none of that changes which
// keyword was named.
TEST(SdfAnnotateTask, ConfigFileKeywordsTolerateQuotesEqualsAndComments) {
  SdfAnnotateConfig config;
  const std::string kCfg = WriteTempFile("cfg_forms.txt",
                                         "# leading comment\n"
                                         "MTM_SPEC = \"MINIMUM\"\n"
                                         "\n"
                                         "SCALE_FACTORS  1.5:2.5:3.5 ; \n"
                                         "// another comment\n"
                                         "SCALE_TYPE\tFROM_TYPICAL\n");
  ASSERT_TRUE(ReadSdfAnnotateConfigFile(kCfg, config));
  EXPECT_EQ(config.mtm_spec, "MINIMUM");
  EXPECT_EQ(config.scale_factors, "1.5:2.5:3.5");
  EXPECT_EQ(config.scale_type, "FROM_TYPICAL");
}

// §32.9: sdf_file is the one required operand of $sdf_annotate, so a call that
// names no file is reported, and the report names §32.9.
TEST(SdfAnnotateTask, MissingSdfFileNames32_9) {
  const std::string kSrc = OneCellDesign("\"\"");
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, kSrc));
  EXPECT_TRUE(ReportedError(d.f.diag.Diagnostics(), "requires an SDF file name",
                            LineHolding(kSrc, "$sdf_annotate"), "32.9"));
}

// §32.9: the legal scale_type keywords are the ones Table 32-6 lists, so a
// call naming another one is warned about, and the warning names §32.9.
TEST(SdfAnnotateTask, UnknownScaleTypeNames32_9) {
  const std::string kSdf = WriteTempFile("st_named.sdf", TripleSdf());
  const std::string kSrc =
      OneCellDesign("\"" + kSdf +
                    "\", , , , \"MAXIMUM\", \"1.0:1.0:1.0\", "
                    "\"FROM_ELSEWHERE\"");
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, kSrc));
  EXPECT_TRUE(ReportedWarning(d.f.diag.Diagnostics(), "unknown scale_type",
                              LineHolding(kSrc, "$sdf_annotate"), "32.9"));
}

}  // namespace
