#include <gtest/gtest.h>

#include <cstdint>
#include <cstdio>
#include <fstream>
#include <ios>
#include <sstream>
#include <string>
#include <string_view>

#include "fixture_sdf_design.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

constexpr uint64_t kTprop = 6;

constexpr uint64_t kSetupLimit = 5;

constexpr uint64_t kNothing = UINT64_MAX;

std::string Stored(std::string_view stem, const std::string& text) {
  std::string path = "/tmp/delta_c32_09e_";
  path.append(stem).append(".sdf");
  std::ofstream(path, std::ios::trunc) << text;
  return path;
}

std::string Quoted(const std::string& text) { return "\"" + text + "\""; }

const char* const kTimedLeaf =
    "module timed_leaf(input i, input c, output o);\n"
    "  specify\n"
    "    specparam tp = 6;\n"
    "    (i => o) = tp;\n"
    "    $setup(i, posedge c, 5);\n"
    "  endspecify\n"
    "endmodule\n";

std::string Cell(std::string_view type, std::string_view instance,
                 const std::string& section) {
  std::string text = " (CELL (CELLTYPE \"";
  text.append(type).append("\") (INSTANCE ").append(instance).append(") ");
  return text + section + ")";
}

std::string Delays(const std::string& entry) {
  return "(DELAY (ABSOLUTE " + entry + "))";
}

std::string LeafPair(const std::string& section) {
  return "(DELAYFILE" + Cell("timed_leaf", "board/p", section) +
         Cell("timed_leaf", "board/q", section) + ")";
}

std::string PairBoard(const std::string& decls, const std::string& stmt) {
  return std::string(kTimedLeaf) +
         "module board;\n"
         "  wire po;\n"
         "  wire qo;\n"
         "  timed_leaf p(1'b0, 1'b0, po);\n"
         "  timed_leaf q(1'b0, 1'b0, qo);\n" +
         decls + "  initial " + stmt + "\nendmodule\n";
}

std::string Call(const std::string& operands) {
  return "$sdf_annotate(" + operands + ");";
}

struct Annotation {
  SdfDesign d;
  SpecifyManager* mgr = nullptr;

  bool Run(const std::string& src) {
    if (!d.Lower(src)) return false;
    mgr = d.f.ctx.GetSpecifyManager();
    if (mgr == nullptr) return false;
    d.f.scheduler.Run();
    return true;
  }

  const PathDelay* Path(std::string_view prefix) const {
    for (const auto& pd : mgr->GetPathDelays()) {
      if (pd.inst_prefix == prefix && pd.dst_port == "o") return &pd;
    }
    return nullptr;
  }

  uint64_t Delay(std::string_view prefix) const {
    const PathDelay* pd = Path(prefix);
    return pd == nullptr ? kNothing : pd->delays[0];
  }

  uint64_t Reject(std::string_view prefix) const {
    const PathDelay* pd = Path(prefix);
    return pd == nullptr ? kNothing : pd->reject_limit[0];
  }

  uint64_t SetupLimit(std::string_view prefix) const {
    for (const auto& tc : mgr->GetTimingChecks()) {
      if (tc.inst_prefix == prefix) return tc.limit;
    }
    return kNothing;
  }
};

bool RunInRegionP(Annotation& a, std::string_view stem,
                  const std::string& section) {
  return a.Run(PairBoard(
      "", Call(Quoted(Stored(stem, LeafPair(section))) + ", board.p")));
}

TEST(SdfAnnotateRegionKinds, DeviceEntryOutsideTheRegionIsNotAnnotated) {
  Annotation a;
  ASSERT_TRUE(RunInRegionP(a, "device", Delays("(DEVICE o (41))")));
  EXPECT_EQ(a.Delay("p."), 41u);
  EXPECT_EQ(a.Delay("q."), kTprop);
}

TEST(SdfAnnotateRegionKinds, PathpulseEntryOutsideTheRegionIsNotAnnotated) {
  Annotation a;
  ASSERT_TRUE(RunInRegionP(a, "pulse", Delays("(PATHPULSE i o (3))")));
  EXPECT_EQ(a.Reject("p."), 3u);
  EXPECT_EQ(a.Reject("q."), kTprop);
}

TEST(SdfAnnotateRegionKinds,
     PathpulsepercentEntryOutsideTheRegionIsNotAnnotated) {
  Annotation a;
  ASSERT_TRUE(
      RunInRegionP(a, "percent", Delays("(PATHPULSEPERCENT i o (50))")));
  EXPECT_EQ(a.Reject("p."), 3u);
  EXPECT_EQ(a.Reject("q."), kTprop);
}

TEST(SdfAnnotateRegionKinds, TimingcheckEntryOutsideTheRegionIsNotAnnotated) {
  Annotation a;
  ASSERT_TRUE(
      RunInRegionP(a, "check", "(TIMINGCHECK (SETUP i (posedge c) (30)))"));
  EXPECT_EQ(a.SetupLimit("p."), 30u);
  EXPECT_EQ(a.SetupLimit("q."), kSetupLimit);
}

TEST(SdfAnnotateRegionKinds, LabelEntryOutsideTheRegionIsNotAnnotated) {
  Annotation a;
  ASSERT_TRUE(RunInRegionP(a, "label", "(LABEL (ABSOLUTE (tp 19)))"));
  EXPECT_EQ(a.Delay("p."), 19u);
  EXPECT_EQ(a.Delay("q."), kTprop);
}

std::string WireBoard(const std::string& sdf_path) {
  return "module fwd(input logic [7:0] din, output logic [7:0] dout);\n"
         "  assign dout = din;\n"
         "endmodule\n"
         "module blk;\n"
         "  logic [7:0] src = 8'h00;\n"
         "  logic [7:0] out;\n"
         "  fwd u(.din(src), .dout(out));\n"
         "  initial #5 src = 8'hA5;\n"
         "endmodule\n"
         "module board;\n"
         "  logic [7:0] src = 8'h00;\n"
         "  logic [7:0] out;\n"
         "  fwd u(.din(src), .dout(out));\n"
         "  blk p();\n"
         "  blk q();\n"
         "  initial #5 src = 8'hA5;\n"
         "  initial #1 $sdf_annotate(\"" +
         sdf_path +
         "\", board.p);\n"
         "  initial #7 $display(\"p=%h q=%h top=%h\", p.out, q.out, out);\n"
         "endmodule\n";
}

std::string WiresSeenAfter(std::string_view stem, const std::string& cells) {
  SimFixture f;
  return RunCapture(WireBoard(Stored(stem, "(DELAYFILE" + cells + ")")), f);
}

std::string BlockPair(const std::string& entry) {
  return Cell("blk", "board/p", Delays(entry)) +
         Cell("blk", "board/q", Delays(entry));
}

TEST(SdfAnnotateRegionKinds, InterconnectEntryOutsideTheRegionIsNotAnnotated) {
  EXPECT_EQ(
      WiresSeenAfter("wire_ic", BlockPair("(INTERCONNECT src u/din (10))")),
      "p=00 q=a5 top=a5\n");
}

TEST(SdfAnnotateRegionKinds, PortEntryOutsideTheRegionIsNotAnnotated) {
  EXPECT_EQ(WiresSeenAfter("wire_port", BlockPair("(PORT u/din (10))")),
            "p=00 q=a5 top=a5\n");
}

TEST(SdfAnnotateRegionKinds, NetdelayEntryOutsideTheRegionIsNotAnnotated) {
  EXPECT_EQ(WiresSeenAfter("wire_net", BlockPair("(NETDELAY u/din (10))")),
            "p=00 q=a5 top=a5\n");
}

TEST(SdfAnnotateRegionKinds, InterconnectPortsAreReadInsideARegionBelowTheTop) {
  EXPECT_EQ(
      WiresSeenAfter("wire_below",
                     Cell("blk", "", Delays("(INTERCONNECT src u/din (10))"))),
      "p=00 q=a5 top=a5\n");
}

std::string MidBoard(const std::string& routine, const std::string& sdf_path) {
  return std::string(kTimedLeaf) +
         "module mid(input i, output o);\n"
         "  timed_leaf inner(i, 1'b0, o);\n" +
         routine + "  initial load(\"" + sdf_path +
         "\");\n"
         "endmodule\n"
         "module board;\n"
         "  wire o1;\n"
         "  wire o2;\n"
         "  mid m1(1'b0, o1);\n"
         "  mid m2(1'b0, o2);\n"
         "endmodule\n";
}

const char* const kLoadTask =
    "  task load(input string f);\n"
    "    $sdf_annotate(f);\n"
    "  endtask\n";

const char* const kLoadFunction =
    "  function void load(input string f);\n"
    "    $sdf_annotate(f);\n"
    "  endfunction\n";

void ExpectEachCallerIsItsOwnRegion(const char* routine, std::string_view tag) {
  const std::string kRelative = Stored(
      std::string(tag) + "_rel",
      "(DELAYFILE" + Cell("timed_leaf", "inner", Delays("(IOPATH i o (10))")) +
          ")");
  Annotation rel;
  ASSERT_TRUE(rel.Run(MidBoard(routine, kRelative)));
  EXPECT_EQ(rel.Delay("m1.inner."), 10u);
  EXPECT_EQ(rel.Delay("m2.inner."), 10u);

  const std::string kRooted =
      Stored(std::string(tag) + "_root",
             "(DELAYFILE" +
                 Cell("timed_leaf", "board/m1/inner",
                      "(DELAY (INCREMENT (IOPATH i o (5))))") +
                 ")");
  Annotation rooted;
  ASSERT_TRUE(rooted.Run(MidBoard(routine, kRooted)));
  EXPECT_EQ(rooted.Delay("m1.inner."), kTprop + 5);
  EXPECT_EQ(rooted.Delay("m2.inner."), kTprop);
}

TEST(SdfAnnotateCallerRegion, CallInATaskOfASubmoduleUsesItsInstance) {
  ExpectEachCallerIsItsOwnRegion(kLoadTask, "task");
}

TEST(SdfAnnotateCallerRegion, CallInAFunctionOfASubmoduleUsesItsInstance) {
  ExpectEachCallerIsItsOwnRegion(kLoadFunction, "func");
}

TEST(SdfAnnotateCallerRegion,
     DISABLED_ModuleInstanceThroughAGenerateBlockNamesItsInstance) {
  const std::string kSdf = Stored(
      "gen_region",
      "(DELAYFILE" +
          Cell("timed_leaf", "board/gb/u", Delays("(IOPATH i o (19))")) +
          Cell("timed_leaf", "board/v", Delays("(IOPATH i o (20))")) + ")");
  Annotation a;
  ASSERT_TRUE(a.Run(std::string(kTimedLeaf) +
                    "module board;\n"
                    "  wire go;\n"
                    "  wire vo;\n"
                    "  if (1) begin : gb\n"
                    "    timed_leaf u(1'b0, 1'b0, go);\n"
                    "  end\n"
                    "  timed_leaf v(1'b0, 1'b0, vo);\n"
                    "  initial $sdf_annotate(\"" +
                    kSdf +
                    "\", board.gb.u);\n"
                    "endmodule\n"));
  EXPECT_EQ(a.Delay("gb_u."), 19u);
  EXPECT_EQ(a.Delay("v."), kTprop);
}

std::string TripleFile(std::string_view stem) {
  return Stored(stem, LeafPair(Delays("(IOPATH i o (10:20:30))")));
}

uint64_t DelayOfPUnder(const std::string& decls, const std::string& stmt) {
  Annotation a;
  EXPECT_TRUE(a.Run(PairBoard(decls, stmt)));
  return a.Delay("p.");
}

TEST(SdfAnnotateStringOperands, IntegralWiderThanTheNameNamesTheFile) {
  const std::string kSdf = TripleFile("wide");
  EXPECT_EQ(DelayOfPUnder("  reg [8*" + std::to_string(kSdf.size() + 3) +
                              ":1] fname = " + Quoted(kSdf) + ";\n",
                          Call("fname, , , , \"MAXIMUM\"")),
            30u);
}

TEST(SdfAnnotateStringOperands, ConcatenatedStringNamesTheFile) {
  TripleFile("joined");
  EXPECT_EQ(DelayOfPUnder("  string dir = \"/tmp\";\n",
                          Call("{dir, \"/delta_c32_09e_joined.sdf\"}, , , , "
                               "\"MAXIMUM\"")),
            30u);
}

TEST(SdfAnnotateStringOperands, MtmSpecHeldInAStringVariableSelects) {
  EXPECT_EQ(DelayOfPUnder("  string mtm = \"MINIMUM\";\n",
                          Call(Quoted(TripleFile("mtm_var")) + ", , , , mtm")),
            10u);
}

TEST(SdfAnnotateStringOperands, IllegalMtmSpecInAStringVariableIsReported) {
  const std::string kSrc =
      PairBoard("  string mtm = \"MOSTLY\";\n",
                Call(Quoted(TripleFile("mtm_bad_var")) + ", , , , mtm"));
  Annotation a;
  ASSERT_TRUE(a.Run(kSrc));
  EXPECT_TRUE(ReportedWarning(a.d.f.diag.Diagnostics(), "unknown mtm_spec",
                              LineHolding(kSrc, "$sdf_annotate"), "32.9"));
}

TEST(SdfAnnotateStringOperands, ScaleFactorsHeldInAStringVariableScale) {
  EXPECT_EQ(DelayOfPUnder("  string factors = \"1.6:1.4:1.2\";\n",
                          Call(Quoted(TripleFile("sf_var")) +
                               ", , , , \"MAXIMUM\", factors")),
            36u);
}

TEST(SdfAnnotateStringOperands, ScaleTypeHeldInAStringVariableSelects) {
  EXPECT_EQ(DelayOfPUnder("  string kind = \"FROM_MINIMUM\";\n",
                          Call(Quoted(TripleFile("st_var")) +
                               ", , , , \"MAXIMUM\", \"2.0:3.0:4.0\", kind")),
            40u);
}

std::string LogText(const std::string& path) {
  std::ifstream in(path);
  std::stringstream text;
  text << in.rdbuf();
  return text.str();
}

TEST(SdfAnnotateStringOperands, LogFileHeldInAStringVariableIsWritten) {
  const std::string kLog = "/tmp/delta_c32_09e_var.log";
  std::remove(kLog.c_str());
  Annotation a;
  ASSERT_TRUE(a.Run(
      PairBoard("  string lf = " + Quoted(kLog) + ";\n",
                Call(Quoted(TripleFile("log_var")) + ", board.p, , lf"))));
  EXPECT_NE(LogText(kLog).find("IOPATH"), std::string::npos);
  std::remove(kLog.c_str());
}

TEST(SdfAnnotateLog, EveryAnnotatingConstructGetsAnEntryThroughTheCall) {
  const std::string kLog = "/tmp/delta_c32_09e_kinds.log";
  std::remove(kLog.c_str());
  const std::string kSdf = Stored(
      "log_kinds",
      "(DELAYFILE" +
          Cell("timed_leaf", "board/p",
               "(DELAY (ABSOLUTE (IOPATH i o (8)) (PATHPULSE i o (2)) "
               "(DEVICE o (9))))") +
          Cell("timed_leaf", "board/p",
               "(TIMINGCHECK (SETUP i (posedge c) (30)))") +
          Cell("timed_leaf", "board/p", "(LABEL (ABSOLUTE (tp 19)))") +
          Cell("board", "board", Delays("(INTERCONNECT p/o q/i (4))")) + ")");
  Annotation a;
  ASSERT_TRUE(
      a.Run(PairBoard("", Call(Quoted(kSdf) + ", , , " + Quoted(kLog)))));
  const std::string kText = LogText(kLog);
  for (const char* kind : {"IOPATH ", "INTERCONNECT ", "DEVICE ", "PATHPULSE ",
                           "TIMINGCHECK ", "SPECPARAM "}) {
    EXPECT_NE(kText.find(kind), std::string::npos) << kind;
  }
  std::remove(kLog.c_str());
}

}  // namespace
