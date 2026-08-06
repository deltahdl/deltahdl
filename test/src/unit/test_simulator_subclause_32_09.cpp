#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>

#include "fixture_sdf_design.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

TEST(SdfParser, ParseEmptyFile) {
  SdfFile file;
  bool ok = ParseSdf("(DELAYFILE)", file);
  EXPECT_TRUE(ok);
  EXPECT_TRUE(file.cells.empty());
}

TEST(SdfParser, ParseVersion) {
  SdfFile file;
  bool ok = ParseSdf(R"((DELAYFILE (SDFVERSION "4.0")))", file);
  EXPECT_TRUE(ok);
  EXPECT_EQ(file.version, "4.0");
}

TEST(SdfParser, ParseDesign) {
  SdfFile file;
  bool ok = ParseSdf(R"((DELAYFILE (DESIGN "top")))", file);
  EXPECT_TRUE(ok);
  EXPECT_EQ(file.design, "top");
}

TEST(SdfMtmKeyword, UnknownStringIsRejectedAndLeavesOutputUntouched) {
  SdfMtmKeyword out = SdfMtmKeyword::kTypical;
  EXPECT_FALSE(ParseSdfMtmKeyword("BOGUS", out));
  EXPECT_EQ(out, SdfMtmKeyword::kTypical);
}

TEST(SdfScaleTypeParser, UnknownStringIsRejectedAndLeavesOutputUntouched) {
  SdfScaleType out = SdfScaleType::kFromTypical;
  EXPECT_FALSE(ParseSdfScaleType("FROM_NOWHERE", out));
  EXPECT_EQ(out, SdfScaleType::kFromTypical);
}

TEST(SdfAnnotationLog, EveryBackannotationCategoryContributesAnEntry) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "mix")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (IOPATH A Z (10))
          (INTERCONNECT s d (5))
          (DEVICE Z (7))
          (PATHPULSE A Z (3))))
        (TIMINGCHECK (SETUP D (posedge CLK) (4)))
        (LABEL (ABSOLUTE (tHold 11)))))
  )",
                       file));

  std::string log_path = "/tmp/sdf_annotate_log_test_categories.log";
  std::remove(log_path.c_str());
  EXPECT_TRUE(WriteSdfAnnotationLog(file, log_path));

  std::ifstream in(log_path);
  ASSERT_TRUE(in.is_open());
  std::stringstream contents;
  contents << in.rdbuf();
  std::string text = contents.str();

  EXPECT_NE(text.find("IOPATH"), std::string::npos);
  EXPECT_NE(text.find("INTERCONNECT"), std::string::npos);
  EXPECT_NE(text.find("DEVICE"), std::string::npos);
  EXPECT_NE(text.find("PATHPULSE"), std::string::npos);
  EXPECT_NE(text.find("TIMINGCHECK"), std::string::npos);
  EXPECT_NE(text.find("SPECPARAM"), std::string::npos);
  std::remove(log_path.c_str());
}

TEST(SdfAnnotationLog, UnwritablePathReportsFailureToCaller) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10))))))
  )",
                       file));

  EXPECT_FALSE(WriteSdfAnnotationLog(
      file, "/tmp/nonexistent_dir_for_sdf_log_test/x.log"));
}

TEST(SdfScaleFactorsParser, SingleValueBroadcastsAcrossAllThreeFactorSlots) {
  SdfScaleFactors out;
  EXPECT_TRUE(ParseSdfScaleFactors("1.6", out));
  EXPECT_DOUBLE_EQ(out.min_factor, 1.6);
  EXPECT_DOUBLE_EQ(out.typ_factor, 1.6);
  EXPECT_DOUBLE_EQ(out.max_factor, 1.6);
}

TEST(SdfScaleFactorsParser, TwoValuePartialTripletBroadcastsTypicalIntoMax) {
  SdfScaleFactors out;
  EXPECT_TRUE(ParseSdfScaleFactors("1.6:1.4", out));
  EXPECT_DOUBLE_EQ(out.min_factor, 1.6);
  EXPECT_DOUBLE_EQ(out.typ_factor, 1.4);
  EXPECT_DOUBLE_EQ(out.max_factor, 1.4);
}

TEST(SdfScaleFactorsParser, MalformedInputIsRejectedAndDoesNotMutateDefaults) {
  SdfScaleFactors out;
  EXPECT_FALSE(ParseSdfScaleFactors("not-a-number", out));
  EXPECT_DOUBLE_EQ(out.min_factor, 1.0);
  EXPECT_DOUBLE_EQ(out.typ_factor, 1.0);
  EXPECT_DOUBLE_EQ(out.max_factor, 1.0);
}

TEST(SdfScaling, ZeroFactorClampsScaledValueToZero) {
  SdfDelayValue v;
  v.min_val = 100;
  v.typ_val = 200;
  v.max_val = 300;
  SdfScaleFactors f;
  f.min_factor = 0.0;
  f.typ_factor = 0.0;
  f.max_factor = 0.0;
  auto out = ApplySdfScaling(v, SdfScaleType::kFromMtm, f);
  EXPECT_EQ(out.min_val, 0u);
  EXPECT_EQ(out.typ_val, 0u);
  EXPECT_EQ(out.max_val, 0u);
}

// ---------------------------------------------------------------------------
// $sdf_annotate as it is actually written: a call in the design's source.
//
// What each operand does depends on how the call was written and on what the
// design already holds, so these tests build the SystemVerilog side from real
// source (parsed, elaborated and lowered, with the declared module paths handed
// to the production collector), put the SDF and configuration files they name
// on disk as real files, and run the design so the calls the source writes are
// what drive the annotation.
// ---------------------------------------------------------------------------

struct Design : SdfDesign {
  bool Build(const std::string& src) {
    if (!SdfDesign::Lower(src)) return false;
    AddPathDelays(Top());
    f.ctx.SetSpecifyManager(&mgr);
    return true;
  }

  void Run() { f.scheduler.Run(); }

  uint64_t Delay(std::string_view src, std::string_view dst) const {
    for (const auto& pd : mgr.GetPathDelays()) {
      if (pd.src_port == src && pd.dst_port == dst) return pd.delays[0];
    }
    return 0;
  }
};

std::string WriteTempFile(const std::string& name, const std::string& text) {
  const std::string kPath = std::string("/tmp/delta_c32_09_") + name;
  std::ofstream out(kPath, std::ios::trunc);
  out << text;
  out.close();
  return kPath;
}

// One cell whose single module path carries three distinct min:typ:max values,
// so the annotated delay reveals which triple member and which scaling the
// call's operands selected.
std::string TripleSdf() {
  return "(DELAYFILE (CELL (CELLTYPE \"leaf\") (INSTANCE top/a) "
         "(DELAY (ABSOLUTE (IOPATH A Z (1:2:3))))))";
}

// The design every operand test annotates: one module path starting at 0, one
// leaf instance for the SDF file's cell to name, and a $sdf_annotate call whose
// operand list the test fills in.
std::string TripleDesign(const std::string& call_args) {
  return "module leaf(input I, output O);\n"
         "endmodule\n"
         "module top(input A, output Z);\n"
         "  leaf a(A, Z);\n"
         "  specify\n"
         "    (A => Z) = 0;\n"
         "  endspecify\n"
         "  initial $sdf_annotate(" +
         call_args +
         ");\n"
         "endmodule\n";
}

// Runs one call over the shared triple-valued SDF file and reports the delay
// the module path ended up holding.
uint64_t AnnotatedTripleDelay(const std::string& file_name,
                              const std::string& trailing_args) {
  const std::string kSdf = WriteTempFile(file_name, TripleSdf());
  Design d;
  EXPECT_TRUE(d.Build(TripleDesign("\"" + kSdf + "\"" + trailing_args)));
  d.Run();
  return d.Delay("A", "Z");
}

// The sdf_file operand as a string literal: the plainest way to name the file
// to be opened.
TEST(SdfAnnotateTask, StringLiteralOperandNamesTheFileToRead) {
  const std::string kSdf =
      WriteTempFile("literal.sdf",
                    "(DELAYFILE (CELL (CELLTYPE \"leaf\") (INSTANCE top/a) "
                    "(DELAY (ABSOLUTE (IOPATH A Z (17))))))");
  Design d;
  ASSERT_TRUE(d.Build(TripleDesign("\"" + kSdf + "\"")));
  d.Run();
  EXPECT_EQ(d.Delay("A", "Z"), 17u);
}

// sdf_file is an expression, so a `string` variable holding the name works the
// same way a literal does.
TEST(SdfAnnotateTask, StringVariableOperandNamesTheFileToRead) {
  const std::string kSdf =
      WriteTempFile("strvar.sdf",
                    "(DELAYFILE (CELL (CELLTYPE \"leaf\") (INSTANCE top/a) "
                    "(DELAY (ABSOLUTE (IOPATH A Z (18))))))");
  const std::string kSrc =
      "module leaf(input I, output O);\n"
      "endmodule\n"
      "module top(input A, output Z);\n"
      "  leaf a(A, Z);\n"
      "  string fname = \"" +
      kSdf +
      "\";\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "  endspecify\n"
      "  initial $sdf_annotate(fname);\n"
      "endmodule\n";

  Design d;
  ASSERT_TRUE(d.Build(kSrc));
  d.Run();
  EXPECT_EQ(d.Delay("A", "Z"), 18u);
}

// An integral variable whose bytes spell the file name is the third form the
// sdf_file operand admits.
TEST(SdfAnnotateTask, IntegralVariableOperandNamesTheFileToRead) {
  const std::string kSdf =
      WriteTempFile("intvar.sdf",
                    "(DELAYFILE (CELL (CELLTYPE \"leaf\") (INSTANCE top/a) "
                    "(DELAY (ABSOLUTE (IOPATH A Z (19))))))");
  const std::string kSrc =
      "module leaf(input I, output O);\n"
      "endmodule\n"
      "module top(input A, output Z);\n"
      "  leaf a(A, Z);\n"
      "  reg [8*" +
      std::to_string(kSdf.size()) + ":1] fname = \"" + kSdf +
      "\";\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "  endspecify\n"
      "  initial $sdf_annotate(fname);\n"
      "endmodule\n";

  Design d;
  ASSERT_TRUE(d.Build(kSrc));
  d.Run();
  EXPECT_EQ(d.Delay("A", "Z"), 19u);
}

// The operand is an expression read when the call runs, so a variable that only
// takes the file name in an earlier statement of the same block still names the
// file the call opens.
TEST(SdfAnnotateTask, SdfFileOperandIsReadWhereTheCallRuns) {
  const std::string kSdf =
      WriteTempFile("assigned.sdf",
                    "(DELAYFILE (CELL (CELLTYPE \"leaf\") (INSTANCE top/a) "
                    "(DELAY (ABSOLUTE (IOPATH A Z (23))))))");
  const std::string kSrc =
      "module leaf(input I, output O);\n"
      "endmodule\n"
      "module top(input A, output Z);\n"
      "  leaf a(A, Z);\n"
      "  string fname;\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "  endspecify\n"
      "  initial begin\n"
      "    fname = \"" +
      kSdf +
      "\";\n"
      "    $sdf_annotate(fname);\n"
      "  end\n"
      "endmodule\n";

  Design d;
  ASSERT_TRUE(d.Build(kSrc));
  d.Run();
  EXPECT_EQ(d.Delay("A", "Z"), 23u);
}

// sdf_file is the one operand a call cannot leave out: with no file named there
// is nothing to read, which is reported rather than passed over.
TEST(SdfAnnotateTask, CallWithNoSdfFileOperandIsReportedAndAnnotatesNothing) {
  Design d;
  ASSERT_TRUE(d.Build(TripleDesign("")));
  d.Run();
  EXPECT_TRUE(d.f.diag.HasErrors());
  EXPECT_EQ(d.Delay("A", "Z"), 0u);
  EXPECT_TRUE(d.mgr.GetSdfAnnotations().empty());
}

// The same holds when the call reaches past an empty first slot to a later
// operand: it still names no file, so there is nothing to read.
TEST(SdfAnnotateTask, CallWithAnEmptySdfFileSlotIsReportedAndAnnotatesNothing) {
  const char* const kSrc =
      "module leaf(input I, output O);\n"
      "endmodule\n"
      "module top(input A, output Z);\n"
      "  leaf a(A, Z);\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "  endspecify\n"
      "  initial $sdf_annotate(, top.a);\n"
      "endmodule\n";

  Design d;
  ASSERT_TRUE(d.Build(kSrc));
  d.Run();
  EXPECT_TRUE(d.f.diag.HasErrors());
  EXPECT_EQ(d.Delay("A", "Z"), 0u);
  EXPECT_TRUE(d.mgr.GetSdfAnnotations().empty());
}

// A file that cannot be opened carries no timing data, so the design keeps what
// it already held and the call is reported.
TEST(SdfAnnotateTask, UnreadableSdfFileIsReportedAndLeavesTheDesignAlone) {
  Design d;
  ASSERT_TRUE(
      d.Build(TripleDesign("\"/tmp/delta_c32_09_absent_dir/none.sdf\"")));
  d.Run();
  EXPECT_EQ(d.Delay("A", "Z"), 0u);
  EXPECT_GT(d.f.diag.WarningCount(), 0u);

  // The call still counts as an annotation of the design having been asked for.
  ASSERT_EQ(d.mgr.GetSdfAnnotations().size(), 1u);
}

// module_instance names the hierarchy level the annotator works from, so a cell
// outside that level is not annotated.
TEST(SdfAnnotateTask, ModuleInstanceOperandSelectsTheHierarchyLevelAnnotated) {
  const std::string kSdf =
      WriteTempFile("scope.sdf",
                    "(DELAYFILE"
                    " (CELL (CELLTYPE \"leaf\") (INSTANCE top/a)"
                    "   (DELAY (ABSOLUTE (IOPATH A Z (10)))))"
                    " (CELL (CELLTYPE \"leaf\") (INSTANCE top/b)"
                    "   (DELAY (ABSOLUTE (IOPATH B Y (20))))))");
  const std::string kSrc =
      "module leaf(input I, output O);\n"
      "endmodule\n"
      "module top(input A, input B, output Z, output Y);\n"
      "  leaf a(A, Z);\n"
      "  leaf b(B, Y);\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "    (B => Y) = 0;\n"
      "  endspecify\n"
      "  initial $sdf_annotate(\"" +
      kSdf +
      "\", top.a);\n"
      "endmodule\n";

  Design d;
  ASSERT_TRUE(d.Build(kSrc));
  d.Run();
  EXPECT_EQ(d.Delay("A", "Z"), 10u);
  EXPECT_EQ(d.Delay("B", "Y"), 0u);
}

// Array indices are permitted in a module_instance, so one element of an
// instance array is a hierarchy level of its own.
TEST(SdfAnnotateTask, ModuleInstanceOperandMayCarryArrayIndices) {
  const std::string kSdf =
      WriteTempFile("indexed.sdf",
                    "(DELAYFILE"
                    " (CELL (CELLTYPE \"leaf\") (INSTANCE top/bank[0])"
                    "   (DELAY (ABSOLUTE (IOPATH A Z (10)))))"
                    " (CELL (CELLTYPE \"leaf\") (INSTANCE top/bank[1])"
                    "   (DELAY (ABSOLUTE (IOPATH B Y (20))))))");
  const std::string kSrc =
      "module leaf(input I, output O);\n"
      "endmodule\n"
      "module top(input A, input B, output Z, output Y);\n"
      "  wire [1:0] ins;\n"
      "  wire [1:0] outs;\n"
      "  leaf bank[1:0](ins, outs);\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "    (B => Y) = 0;\n"
      "  endspecify\n"
      "  initial $sdf_annotate(\"" +
      kSdf +
      "\", top.bank[1]);\n"
      "endmodule\n";

  Design d;
  ASSERT_TRUE(d.Build(kSrc));
  d.Run();
  EXPECT_EQ(d.Delay("A", "Z"), 0u);
  EXPECT_EQ(d.Delay("B", "Y"), 20u);
}

// An index is an expression, so an element may be picked out by a constant the
// design declares rather than by a plain number written in the call.
TEST(SdfAnnotateTask, ModuleInstanceIndexMayBeWrittenAsADeclaredConstant) {
  const std::string kSdf =
      WriteTempFile("indexed_param.sdf",
                    "(DELAYFILE"
                    " (CELL (CELLTYPE \"leaf\") (INSTANCE top/bank[0])"
                    "   (DELAY (ABSOLUTE (IOPATH A Z (10)))))"
                    " (CELL (CELLTYPE \"leaf\") (INSTANCE top/bank[1])"
                    "   (DELAY (ABSOLUTE (IOPATH B Y (20))))))");
  const std::string kSrc =
      "module leaf(input I, output O);\n"
      "endmodule\n"
      "module top(input A, input B, output Z, output Y);\n"
      "  wire [1:0] ins;\n"
      "  wire [1:0] outs;\n"
      "  leaf bank[1:0](ins, outs);\n"
      "  localparam int SEL = 1;\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "    (B => Y) = 0;\n"
      "  endspecify\n"
      "  initial $sdf_annotate(\"" +
      kSdf +
      "\", top.bank[SEL]);\n"
      "endmodule\n";

  Design d;
  ASSERT_TRUE(d.Build(kSrc));
  d.Run();
  EXPECT_EQ(d.Delay("A", "Z"), 0u);
  EXPECT_EQ(d.Delay("B", "Y"), 20u);
}

// An index part way along a hierarchical path is an ordinary module_instance
// too: the level named here sits below an indexed instance.
TEST(SdfAnnotateTask, ModuleInstanceMayIndexPartWayAlongAPath) {
  const std::string kSdf =
      WriteTempFile("indexed_deep.sdf",
                    "(DELAYFILE"
                    " (CELL (CELLTYPE \"core\") (INSTANCE top/bank[0]/c)"
                    "   (DELAY (ABSOLUTE (IOPATH A Z (10)))))"
                    " (CELL (CELLTYPE \"core\") (INSTANCE top/bank[1]/c)"
                    "   (DELAY (ABSOLUTE (IOPATH B Y (26))))))");
  const std::string kSrc =
      "module core(input I, output O);\n"
      "endmodule\n"
      "module blk(input I, output O);\n"
      "  core c(I, O);\n"
      "endmodule\n"
      "module top(input A, input B, output Z, output Y);\n"
      "  wire [1:0] ins;\n"
      "  wire [1:0] outs;\n"
      "  blk bank[1:0](ins, outs);\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "    (B => Y) = 0;\n"
      "  endspecify\n"
      "  initial $sdf_annotate(\"" +
      kSdf +
      "\", top.bank[1].c);\n"
      "endmodule\n";

  Design d;
  ASSERT_TRUE(d.Build(kSrc));
  d.Run();
  EXPECT_EQ(d.Delay("A", "Z"), 0u);
  EXPECT_EQ(d.Delay("B", "Y"), 26u);
}

// A module_instance may be a bare instance name rather than a dotted path, in
// which case it names that instance's level directly.
TEST(SdfAnnotateTask, ModuleInstanceMayBeABareInstanceName) {
  const std::string kSdf =
      WriteTempFile("bare.sdf",
                    "(DELAYFILE"
                    " (CELL (CELLTYPE \"leaf\") (INSTANCE a)"
                    "   (DELAY (ABSOLUTE (IOPATH A Z (24)))))"
                    " (CELL (CELLTYPE \"leaf\") (INSTANCE b)"
                    "   (DELAY (ABSOLUTE (IOPATH B Y (25))))))");
  const std::string kSrc =
      "module leaf(input I, output O);\n"
      "endmodule\n"
      "module top(input A, input B, output Z, output Y);\n"
      "  leaf a(A, Z);\n"
      "  leaf b(B, Y);\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "    (B => Y) = 0;\n"
      "  endspecify\n"
      "  initial $sdf_annotate(\"" +
      kSdf +
      "\", a);\n"
      "endmodule\n";

  Design d;
  ASSERT_TRUE(d.Build(kSrc));
  d.Run();
  EXPECT_EQ(d.Delay("A", "Z"), 24u);
  EXPECT_EQ(d.Delay("B", "Y"), 0u);
}

// A module_instance names a level of the hierarchy, not a run of characters:
// a cell whose path merely starts with the same text is at a different level
// and is left alone, and so is a cell sitting above the named level. The third
// cell here really is inside the named level, so the file is demonstrably being
// read and it is the level test that keeps the other two out.
TEST(SdfAnnotateTask, ModuleInstanceSelectsAHierarchyLevelNotATextualPrefix) {
  const std::string kSdf =
      WriteTempFile("level.sdf",
                    "(DELAYFILE"
                    " (CELL (CELLTYPE \"leaf\") (INSTANCE top/ax)"
                    "   (DELAY (ABSOLUTE (IOPATH A Z (10)))))"
                    " (CELL (CELLTYPE \"leaf\") (INSTANCE top)"
                    "   (DELAY (ABSOLUTE (IOPATH B Y (20)))))"
                    " (CELL (CELLTYPE \"leaf\") (INSTANCE top/a/deep)"
                    "   (DELAY (ABSOLUTE (IOPATH C W (30))))))");
  const std::string kSrc =
      "module leaf(input I, output O);\n"
      "endmodule\n"
      "module top(input A, input B, input C, output Z, output Y, output W);\n"
      "  leaf a(A, Z);\n"
      "  leaf ax(B, Y);\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "    (B => Y) = 0;\n"
      "    (C => W) = 0;\n"
      "  endspecify\n"
      "  initial $sdf_annotate(\"" +
      kSdf +
      "\", top.a);\n"
      "endmodule\n";

  Design d;
  ASSERT_TRUE(d.Build(kSrc));
  d.Run();
  EXPECT_EQ(d.Delay("A", "Z"), 0u);
  EXPECT_EQ(d.Delay("B", "Y"), 0u);
  EXPECT_EQ(d.Delay("C", "W"), 30u);
}

// With module_instance left out, the annotator works from the module that holds
// the call, so a cell outside that module's hierarchy is not annotated.
TEST(SdfAnnotateTask, OmittedModuleInstanceUsesTheModuleHoldingTheCall) {
  const std::string kSdf =
      WriteTempFile("default_scope.sdf",
                    "(DELAYFILE"
                    " (CELL (CELLTYPE \"leaf\") (INSTANCE top/a)"
                    "   (DELAY (ABSOLUTE (IOPATH A Z (10)))))"
                    " (CELL (CELLTYPE \"leaf\") (INSTANCE elsewhere/b)"
                    "   (DELAY (ABSOLUTE (IOPATH B Y (20))))))");
  const std::string kSrc =
      "module leaf(input I, output O);\n"
      "endmodule\n"
      "module top(input A, input B, output Z, output Y);\n"
      "  leaf a(A, Z);\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "    (B => Y) = 0;\n"
      "  endspecify\n"
      "  initial $sdf_annotate(\"" +
      kSdf +
      "\");\n"
      "endmodule\n";

  Design d;
  ASSERT_TRUE(d.Build(kSrc));
  d.Run();
  EXPECT_EQ(d.Delay("A", "Z"), 10u);
  EXPECT_EQ(d.Delay("B", "Y"), 0u);
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
  Design d;
  ASSERT_TRUE(d.Build(TripleDesign("\"" + kSdf + "\", , , , \"MOSTLY\"")));
  d.Run();
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
  const std::string kSdf =
      WriteTempFile("sf_positional.sdf",
                    "(DELAYFILE (CELL (CELLTYPE \"leaf\") (INSTANCE top/a) "
                    "(DELAY (ABSOLUTE (IOPATH A Z (10:20:30))))))");

  auto under = [&](const std::string& mtm) {
    Design d;
    EXPECT_TRUE(d.Build(TripleDesign("\"" + kSdf + "\", , , , \"" + mtm +
                                     "\", \"1.6:1.4:1.2\"")));
    d.Run();
    return d.Delay("A", "Z");
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
  Design d;
  ASSERT_TRUE(d.Build(TripleDesign(
      "\"" + kSdf +
      "\", , , , \"MAXIMUM\", \"1.0:1.0:1.0\", \"FROM_NOWHERE\"")));
  d.Run();
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
  Design d;
  ASSERT_TRUE(d.Build(TripleDesign(
      "\"" + kSdf + "\", , \"/tmp/delta_c32_09_absent_dir/cfg.txt\"")));
  d.Run();
  EXPECT_GT(d.f.diag.WarningCount(), 0u);
  EXPECT_EQ(d.Delay("A", "Z"), 2u);
}

// The configuration file is named by an ordinary character-string operand, so a
// variable holding the name works the same way a literal does.
TEST(SdfAnnotateTask, ConfigFileMayBeNamedByAStringVariable) {
  const std::string kSdf = WriteTempFile("cfg_var.sdf", TripleSdf());
  const std::string kCfg = WriteTempFile("cfg_var.txt", "MTM_SPEC MAXIMUM;\n");
  const std::string kSrc =
      "module leaf(input I, output O);\n"
      "endmodule\n"
      "module top(input A, output Z);\n"
      "  leaf a(A, Z);\n"
      "  string cfg = \"" +
      kCfg +
      "\";\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "  endspecify\n"
      "  initial $sdf_annotate(\"" +
      kSdf +
      "\", , cfg);\n"
      "endmodule\n";

  Design d;
  ASSERT_TRUE(d.Build(kSrc));
  d.Run();
  EXPECT_EQ(d.Delay("A", "Z"), 3u);
}

// A log file that cannot be written is reported, and the annotation the call
// asked for still lands.
TEST(SdfAnnotateTask, UnwritableLogFileIsReported) {
  const std::string kSdf =
      WriteTempFile("log_absent.sdf",
                    "(DELAYFILE (CELL (CELLTYPE \"leaf\") (INSTANCE top/a) "
                    "(DELAY (ABSOLUTE (IOPATH A Z (28))))))");
  Design d;
  ASSERT_TRUE(d.Build(TripleDesign(
      "\"" + kSdf + "\", , , \"/tmp/delta_c32_09_absent_dir/run.log\"")));
  d.Run();
  EXPECT_EQ(d.Delay("A", "Z"), 28u);
  EXPECT_GT(d.f.diag.WarningCount(), 0u);
}

// With a log_file named, each individual annotation the SDF file carries earns
// its own entry in it.
TEST(SdfAnnotateTask, LogFileOperandRecordsAnEntryPerIndividualAnnotation) {
  const std::string kSdf =
      WriteTempFile("logged.sdf",
                    "(DELAYFILE (CELL (CELLTYPE \"leaf\") (INSTANCE top/a) "
                    "(DELAY (ABSOLUTE"
                    " (IOPATH A Z (10))"
                    " (IOPATH B Z (11))"
                    " (IOPATH C Z (12))))))");
  const std::string kLog = std::string("/tmp/delta_c32_09_run.log");
  std::remove(kLog.c_str());

  Design d;
  ASSERT_TRUE(d.Build(TripleDesign("\"" + kSdf + "\", , , \"" + kLog + "\"")));
  d.Run();

  std::ifstream in(kLog);
  ASSERT_TRUE(in.is_open());
  std::size_t lines = 0;
  std::string line;
  while (std::getline(in, line)) {
    if (!line.empty()) ++lines;
  }
  EXPECT_EQ(lines, 3u);
  std::remove(kLog.c_str());
}

// The log records the annotations a call actually made, so a call aimed at one
// region leaves out the entries for cells that region does not cover.
TEST(SdfAnnotateTask, LogFileRecordsOnlyAnnotationsInsideTheNamedRegion) {
  const std::string kSdf =
      WriteTempFile("logged_scoped.sdf",
                    "(DELAYFILE"
                    " (CELL (CELLTYPE \"leaf\") (INSTANCE top/a)"
                    "   (DELAY (ABSOLUTE (IOPATH A Z (10)))))"
                    " (CELL (CELLTYPE \"leaf\") (INSTANCE top/b)"
                    "   (DELAY (ABSOLUTE (IOPATH B Y (20))))))");
  const std::string kLog = std::string("/tmp/delta_c32_09_scoped.log");
  std::remove(kLog.c_str());

  const std::string kSrc =
      "module leaf(input I, output O);\n"
      "endmodule\n"
      "module top(input A, input B, output Z, output Y);\n"
      "  leaf a(A, Z);\n"
      "  leaf b(B, Y);\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "    (B => Y) = 0;\n"
      "  endspecify\n"
      "  initial $sdf_annotate(\"" +
      kSdf + "\", top.a, , \"" + kLog +
      "\");\n"
      "endmodule\n";

  Design d;
  ASSERT_TRUE(d.Build(kSrc));
  d.Run();

  // Only the cell inside the named region was annotated.
  EXPECT_EQ(d.Delay("A", "Z"), 10u);
  EXPECT_EQ(d.Delay("B", "Y"), 0u);

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
      WriteTempFile("unlogged.sdf",
                    "(DELAYFILE (CELL (CELLTYPE \"leaf\") (INSTANCE top/a) "
                    "(DELAY (ABSOLUTE (IOPATH A Z (14))))))");
  const std::string kLog = std::string("/tmp/delta_c32_09_unwritten.log");
  std::remove(kLog.c_str());

  Design d;
  ASSERT_TRUE(d.Build(TripleDesign("\"" + kSdf + "\"")));
  d.Run();

  EXPECT_EQ(d.Delay("A", "Z"), 14u);
  std::ifstream in(kLog);
  EXPECT_FALSE(in.is_open());
}

// §32.6 annotates more than one SDF file in turn; when two calls name one log
// file, the entries of both are in it rather than the later call's alone.
TEST(SdfAnnotateTask, TwoCallsNamingOneLogFileBothContributeEntries) {
  const std::string kSdf1 =
      WriteTempFile("logged_a.sdf",
                    "(DELAYFILE (CELL (CELLTYPE \"leaf\") (INSTANCE top/a) "
                    "(DELAY (ABSOLUTE (IOPATH A Z (10)) (IOPATH B Z (11))))))");
  const std::string kSdf2 =
      WriteTempFile("logged_b.sdf",
                    "(DELAYFILE (CELL (CELLTYPE \"leaf\") (INSTANCE top/a) "
                    "(DELAY (ABSOLUTE (IOPATH C Z (12))))))");
  const std::string kLog = std::string("/tmp/delta_c32_09_two_calls.log");
  std::remove(kLog.c_str());

  const std::string kSrc =
      "module leaf(input I, output O);\n"
      "endmodule\n"
      "module top(input A, output Z);\n"
      "  leaf a(A, Z);\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "  endspecify\n"
      "  initial begin\n"
      "    $sdf_annotate(\"" +
      kSdf1 + "\", , , \"" + kLog +
      "\");\n"
      "    $sdf_annotate(\"" +
      kSdf2 + "\", , , \"" + kLog +
      "\");\n"
      "  end\n"
      "endmodule\n";

  Design d;
  ASSERT_TRUE(d.Build(kSrc));
  d.Run();

  std::ifstream in(kLog);
  ASSERT_TRUE(in.is_open());
  std::size_t lines = 0;
  std::string line;
  while (std::getline(in, line)) {
    if (!line.empty()) ++lines;
  }
  EXPECT_EQ(lines, 3u);
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

}  // namespace
