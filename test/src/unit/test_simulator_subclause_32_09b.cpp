#include <gtest/gtest.h>

#include <cstdint>
#include <cstdio>
#include <fstream>
#include <ios>
#include <sstream>
#include <string>
#include <string_view>
#include <utility>

#include "fixture_sdf_design.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

constexpr uint64_t kDeclaredDelay = 7;

constexpr uint64_t kNoPath = UINT64_MAX;

bool BuildAndRun(SdfDesign& d, const std::string& src) {
  if (!d.Lower(src)) return false;
  d.f.scheduler.Run();
  return true;
}

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

std::string CellRecord(const std::string& instance, const std::string& delay) {
  return " (CELL (CELLTYPE \"timed_cell\") (INSTANCE " + instance +
         ") (DELAY (ABSOLUTE (IOPATH A Z (" + delay + ")))))";
}

std::string DelayFile(const std::string& cells) {
  return "(DELAYFILE" + cells + ")";
}

std::string TripleSdf() { return DelayFile(CellRecord("top/a", "1:2:3")); }

std::string OneCellSource(const std::string& decls, const std::string& body) {
  return CellDecl("timed_cell") +
         "module top;\n"
         "  wire src;\n"
         "  wire dst;\n"
         "  timed_cell a(src, dst);\n" +
         decls + "  initial " + body + "\n" + "endmodule\n";
}

std::string OneCellDesign(const std::string& call_args) {
  return OneCellSource("", "$sdf_annotate(" + call_args + ");");
}

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

uint64_t AnnotatedTripleDelay(const std::string& file_name,
                              const std::string& trailing_args) {
  const std::string kSdf = WriteTempFile(file_name, TripleSdf());
  SdfDesign d;
  EXPECT_TRUE(
      BuildAndRun(d, OneCellDesign("\"" + kSdf + "\"" + trailing_args)));
  return DelayIn(d, "a.");
}

TEST(SdfAnnotateTask, StringLiteralOperandNamesTheFileToRead) {
  const std::string kSdf =
      WriteTempFile("literal.sdf", DelayFile(CellRecord("top/a", "17")));
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, OneCellDesign("\"" + kSdf + "\"")));
  EXPECT_EQ(DelayIn(d, "a."), 17u);
}

TEST(SdfAnnotateTask, StringVariableOperandNamesTheFileToRead) {
  const std::string kSdf =
      WriteTempFile("strvar.sdf", DelayFile(CellRecord("top/a", "18")));
  SdfDesign d;
  ASSERT_TRUE(
      BuildAndRun(d, OneCellSource("  string fname = \"" + kSdf + "\";\n",
                                   "$sdf_annotate(fname);")));
  EXPECT_EQ(DelayIn(d, "a."), 18u);
}

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

TEST(SdfAnnotateTask, CallWithNoSdfFileOperandIsReportedAndAnnotatesNothing) {
  const std::string kSrc = OneCellDesign("");
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, kSrc));
  EXPECT_TRUE(ReportedError(d.f.diag.Diagnostics(),
                            "$sdf_annotate requires an SDF file name",
                            LineHolding(kSrc, "$sdf_annotate"), "32.9"));
  EXPECT_EQ(DelayIn(d, "a."), kDeclaredDelay);
}

TEST(SdfAnnotateTask, CallWithAnEmptySdfFileSlotIsReportedAndAnnotatesNothing) {
  const std::string kSrc = OneCellDesign(", top.a");
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, kSrc));
  EXPECT_TRUE(ReportedError(d.f.diag.Diagnostics(),
                            "$sdf_annotate requires an SDF file name",
                            LineHolding(kSrc, "$sdf_annotate"), "32.9"));
  EXPECT_EQ(DelayIn(d, "a."), kDeclaredDelay);
}

TEST(SdfAnnotateTask, UnreadableSdfFileIsReportedAndLeavesTheDesignAlone) {
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(
      d, OneCellDesign("\"/tmp/delta_c32_09_absent_dir/none.sdf\"")));
  EXPECT_EQ(DelayIn(d, "a."), kDeclaredDelay);
  EXPECT_GT(d.f.diag.WarningCount(), 0u);
}

TEST(SdfAnnotateTask, ModuleInstanceOperandSelectsTheHierarchyLevelAnnotated) {
  const std::string kSdf = WriteTempFile(
      "scope.sdf",
      DelayFile(CellRecord("top/a", "10") + CellRecord("top/b", "20")));
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, TwoCellDesign("\"" + kSdf + "\", top.a")));
  EXPECT_EQ(DelayIn(d, "a."), 10u);
  EXPECT_EQ(DelayIn(d, "b."), kDeclaredDelay);
}

TEST(SdfAnnotateTask, ModuleInstanceOperandMayCarryArrayIndices) {
  const std::string kSdf =
      WriteTempFile("indexed.sdf", DelayFile(CellRecord("top/bank[0]", "10") +
                                             CellRecord("top/bank[1]", "20")));
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, BankDesign("", "\"" + kSdf + "\", top.bank[1]")));
  EXPECT_EQ(DelayIn(d, "bank[0]."), kDeclaredDelay);
  EXPECT_EQ(DelayIn(d, "bank[1]."), 20u);
}

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

TEST(SdfAnnotateTask, ModuleInstanceMayBeABareInstanceName) {
  const std::string kSdf = WriteTempFile(
      "bare.sdf",
      DelayFile(CellRecord("top/a", "24") + CellRecord("top/b", "25")));
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, TwoCellDesign("\"" + kSdf + "\", a")));
  EXPECT_EQ(DelayIn(d, "a."), 24u);
  EXPECT_EQ(DelayIn(d, "b."), kDeclaredDelay);
}

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

TEST(SdfAnnotateTask, OmittedModuleInstanceUsesTheModuleHoldingTheCall) {
  const std::string kSdf = WriteTempFile(
      "default_scope.sdf",
      DelayFile(CellRecord("top/a", "10") + CellRecord("elsewhere/b", "20")));
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, TwoCellDesign("\"" + kSdf + "\"")));
  EXPECT_EQ(DelayIn(d, "a."), 10u);
  EXPECT_EQ(DelayIn(d, "b."), kDeclaredDelay);
}

TEST(SdfAnnotateTask, CellPathIsRelativeToTheModuleHoldingTheCall) {
  const std::string kSdf =
      WriteTempFile("relative_to_caller.sdf", DelayFile(CellRecord("a", "10")));
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, TwoCellDesign("\"" + kSdf + "\"")));
  EXPECT_EQ(DelayIn(d, "a."), 10u);
  EXPECT_EQ(DelayIn(d, "b."), kDeclaredDelay);
}

TEST(SdfAnnotateTask, CellWithNoInstancePathIsTheRegion) {
  const std::string kSdf =
      WriteTempFile("empty_instance.sdf", DelayFile(CellRecord("", "15")));
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, TwoCellDesign("\"" + kSdf + "\", a")));
  EXPECT_EQ(DelayIn(d, "a."), 15u);
  EXPECT_EQ(DelayIn(d, "b."), kDeclaredDelay);
}

TEST(SdfAnnotateTask, ValuesAreScaledFromTheFilesTimescaleToThePrecision) {
  const std::string kUnits = "  timeunit 1ns; timeprecision 1ps;\n";
  std::string timed = TwoCellDesign("\"%s\"");
  for (const std::string kHeader :
       {"module timed_cell(input A, output Z);\n", "module top;\n"}) {
    timed.insert(timed.find(kHeader) + kHeader.size(), kUnits);
  }
  auto run = [&](const std::string& name, const std::string& file) {
    const std::string kSdf = WriteTempFile(name, file);
    std::string src = timed;
    src.replace(src.find("%s"), 2, kSdf);
    SdfDesign d;
    EXPECT_TRUE(BuildAndRun(d, src));
    return DelayIn(d, "a.");
  };
  EXPECT_EQ(run("ts_100ps.sdf",
                DelayFile(" (TIMESCALE 100ps)" + CellRecord("top/a", "30"))),
            3000u);
  EXPECT_EQ(run("ts_default.sdf", DelayFile(CellRecord("top/a", "4"))), 4000u);
  EXPECT_EQ(run("ts_real.sdf",
                DelayFile(" (TIMESCALE 1 ns)" + CellRecord("top/a", "2.5"))),
            2500u);
}

std::string MidDesign(const std::string& call, bool call_in_mid) {
  return CellDecl("timed_cell") +
         "module mid(input A, output Z);\n"
         "  timed_cell inner(A, Z);\n" +
         (call_in_mid ? "  initial " + call + "\n" : std::string()) +
         "endmodule\n"
         "module top;\n"
         "  wire src;\n"
         "  wire o1;\n"
         "  wire o2;\n"
         "  mid m1(src, o1);\n"
         "  mid m2(src, o2);\n" +
         (call_in_mid ? std::string() : "  initial " + call + "\n") +
         "endmodule\n";
}

TEST(SdfAnnotateTask, CallInASubmoduleAnnotatesFromTheCallingInstance) {
  const std::string kRelative =
      WriteTempFile("call_in_mid.sdf", DelayFile(CellRecord("inner", "10")));
  SdfDesign rel;
  ASSERT_TRUE(BuildAndRun(
      rel, MidDesign("$sdf_annotate(\"" + kRelative + "\");", true)));
  EXPECT_EQ(DelayIn(rel, "m1.inner."), 10u);
  EXPECT_EQ(DelayIn(rel, "m2.inner."), 10u);

  const std::string kRooted = WriteTempFile(
      "call_in_mid_rooted.sdf",
      "(DELAYFILE (CELL (CELLTYPE \"timed_cell\") (INSTANCE top/m1/inner)"
      " (DELAY (INCREMENT (IOPATH A Z (5))))))");
  SdfDesign rooted;
  ASSERT_TRUE(BuildAndRun(
      rooted, MidDesign("$sdf_annotate(\"" + kRooted + "\");", true)));
  EXPECT_EQ(DelayIn(rooted, "m1.inner."), kDeclaredDelay + 5);
  EXPECT_EQ(DelayIn(rooted, "m2.inner."), kDeclaredDelay);
}

TEST(SdfAnnotateTask, ModuleInstanceIsTheRegionCellPathsAreReadFrom) {
  const std::string kRelative = WriteTempFile(
      "region_relative.sdf", DelayFile(CellRecord("inner", "11")));
  SdfDesign rel;
  ASSERT_TRUE(BuildAndRun(
      rel, MidDesign("$sdf_annotate(\"" + kRelative + "\", m2);", false)));
  EXPECT_EQ(DelayIn(rel, "m1.inner."), kDeclaredDelay);
  EXPECT_EQ(DelayIn(rel, "m2.inner."), 11u);

  const std::string kRooted = WriteTempFile(
      "region_rooted.sdf", DelayFile(CellRecord("top/m2/inner", "12") +
                                     CellRecord("top/m1/inner", "13")));
  SdfDesign rooted;
  ASSERT_TRUE(BuildAndRun(
      rooted, MidDesign("$sdf_annotate(\"" + kRooted + "\", m2);", false)));
  EXPECT_EQ(DelayIn(rooted, "m1.inner."), kDeclaredDelay);
  EXPECT_EQ(DelayIn(rooted, "m2.inner."), 12u);

  SdfDesign deep;
  ASSERT_TRUE(BuildAndRun(
      deep,
      MidDesign("$sdf_annotate(\"" + kRooted + "\", top.m2.inner);", false)));
  EXPECT_EQ(DelayIn(deep, "m1.inner."), kDeclaredDelay);
  EXPECT_EQ(DelayIn(deep, "m2.inner."), 12u);
}

TEST(SdfAnnotateTask, MtmSpecOperandSelectsTheTripleMemberAnnotated) {
  EXPECT_EQ(AnnotatedTripleDelay("mtm_min.sdf", ", , , , \"MINIMUM\""), 1u);
  EXPECT_EQ(AnnotatedTripleDelay("mtm_typ.sdf", ", , , , \"TYPICAL\""), 2u);
  EXPECT_EQ(AnnotatedTripleDelay("mtm_max.sdf", ", , , , \"MAXIMUM\""), 3u);
}

TEST(SdfAnnotateTask, ToolControlIsTheMtmSpecDefault) {
  const uint64_t kExplicit =
      AnnotatedTripleDelay("mtm_tool.sdf", ", , , , \"TOOL_CONTROL\"");
  const uint64_t kOmitted = AnnotatedTripleDelay("mtm_none.sdf", "");
  EXPECT_EQ(kExplicit, kOmitted);
}

TEST(SdfAnnotateTask, UnknownMtmSpecKeywordIsReported) {
  const std::string kSdf = WriteTempFile("mtm_bogus.sdf", TripleSdf());
  SdfDesign d;
  ASSERT_TRUE(
      BuildAndRun(d, OneCellDesign("\"" + kSdf + "\", , , , \"MOSTLY\"")));
  EXPECT_GT(d.f.diag.WarningCount(), 0u);
}

TEST(SdfAnnotateTask, DefaultScaleFactorsLeaveTheAnnotatedValuesAsWritten) {
  EXPECT_EQ(AnnotatedTripleDelay("sf_none.sdf", ", , , , \"MAXIMUM\""), 3u);
  EXPECT_EQ(AnnotatedTripleDelay("sf_unit.sdf",
                                 ", , , , \"MAXIMUM\", \"1.0:1.0:1.0\""),
            3u);
}

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

TEST(SdfAnnotateTask, FromMtmIsTheScaleTypeDefault) {
  const uint64_t kExplicit = AnnotatedTripleDelay(
      "st_default_explicit.sdf",
      ", , , , \"MAXIMUM\", \"2.0:3.0:4.0\", \"FROM_MTM\"");
  const uint64_t kOmitted = AnnotatedTripleDelay(
      "st_default_omitted.sdf", ", , , , \"MAXIMUM\", \"2.0:3.0:4.0\"");
  EXPECT_EQ(kExplicit, kOmitted);
  EXPECT_EQ(kExplicit, 12u);
}

TEST(SdfAnnotateTask, UnknownScaleTypeKeywordIsReported) {
  const std::string kSdf = WriteTempFile("st_bogus.sdf", TripleSdf());
  SdfDesign d;
  ASSERT_TRUE(
      BuildAndRun(d, OneCellDesign("\"" + kSdf +
                                   "\", , , , \"MAXIMUM\", \"1.0:1.0:1.0\", "
                                   "\"FROM_NOWHERE\"")));
  EXPECT_GT(d.f.diag.WarningCount(), 0u);
}

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

TEST(SdfAnnotateTask, MtmSpecOperandOverridesTheConfigFileKeyword) {
  const std::string kCfg = WriteTempFile("ovr_mtm.txt", "MTM_SPEC MAXIMUM;\n");
  EXPECT_EQ(AnnotatedTripleDelay("ovr_mtm.sdf",
                                 ", , \"" + kCfg + "\", , \"MINIMUM\""),
            1u);
}

TEST(SdfAnnotateTask, ScaleFactorsOperandOverridesTheConfigFileKeyword) {
  const std::string kCfg =
      WriteTempFile("ovr_factors.txt", "SCALE_FACTORS 2.0:2.0:2.0;\n");
  EXPECT_EQ(AnnotatedTripleDelay(
                "ovr_factors.sdf",
                ", , \"" + kCfg + "\", , \"MAXIMUM\", \"3.0:3.0:3.0\""),
            9u);
}

TEST(SdfAnnotateTask, ScaleTypeOperandOverridesTheConfigFileKeyword) {
  const std::string kCfg =
      WriteTempFile("ovr_type.txt", "SCALE_TYPE FROM_MAXIMUM;\n");
  EXPECT_EQ(AnnotatedTripleDelay("ovr_type.sdf",
                                 ", , \"" + kCfg +
                                     "\", , \"MAXIMUM\", \"1.0:1.0:1.0\", "
                                     "\"FROM_MINIMUM\""),
            1u);
}

TEST(SdfAnnotateTask, UnreadableConfigFileIsReported) {
  const std::string kSdf = WriteTempFile("cfg_absent.sdf", TripleSdf());
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(
      d, OneCellDesign("\"" + kSdf +
                       "\", , \"/tmp/delta_c32_09_absent_dir/cfg.txt\"")));
  EXPECT_GT(d.f.diag.WarningCount(), 0u);
  EXPECT_EQ(DelayIn(d, "a."), 2u);
}

TEST(SdfAnnotateTask, ConfigFileMayBeNamedByAStringVariable) {
  const std::string kSdf = WriteTempFile("cfg_var.sdf", TripleSdf());
  const std::string kCfg = WriteTempFile("cfg_var.txt", "MTM_SPEC MAXIMUM;\n");
  SdfDesign d;
  ASSERT_TRUE(
      BuildAndRun(d, OneCellSource("  string cfg = \"" + kCfg + "\";\n",
                                   "$sdf_annotate(\"" + kSdf + "\", , cfg);")));
  EXPECT_EQ(DelayIn(d, "a."), 3u);
}

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

TEST(SdfAnnotateTask, LogFileRecordsOnlyAnnotationsInsideTheNamedRegion) {
  const std::string kSdf = WriteTempFile(
      "logged_scoped.sdf",
      DelayFile(CellRecord("top/a", "10") + CellRecord("top/b", "20")));
  const std::string kLog = std::string("/tmp/delta_c32_09_scoped.log");
  std::remove(kLog.c_str());

  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(
      d, TwoCellDesign("\"" + kSdf + "\", top.a, , \"" + kLog + "\"")));

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

TEST(SdfAnnotateTask, MissingSdfFileNames32_9) {
  const std::string kSrc = OneCellDesign("\"\"");
  SdfDesign d;
  ASSERT_TRUE(BuildAndRun(d, kSrc));
  EXPECT_TRUE(ReportedError(d.f.diag.Diagnostics(), "requires an SDF file name",
                            LineHolding(kSrc, "$sdf_annotate"), "32.9"));
}

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
