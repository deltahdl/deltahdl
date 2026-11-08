#include <gtest/gtest.h>

#include <cstdint>
#include <fstream>
#include <ios>
#include <string>
#include <string_view>

#include "fixture_sdf_design.h"
#include "fixture_simulator.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

struct Annotated : SdfDesign {
  SpecifyManager* run_mgr = nullptr;

  bool Build(const std::string& src) {
    if (!SdfDesign::Lower(src)) return false;
    run_mgr = f.ctx.GetSpecifyManager();
    return run_mgr != nullptr;
  }

  void Run() { f.scheduler.Run(); }

  const ModuleDecl& Cell() const { return *cu->modules.front(); }

  void AddTimingChecksOf(const ModuleDecl& mod) {
    for (auto* item : mod.items) {
      if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
      for (auto* si : item->specify_items) {
        if (si->kind != SpecifyItemKind::kTimingCheck) continue;
        run_mgr->AddTimingCheckUnderOptions(si->timing_check, f.ctx, f.arena);
      }
    }
  }

  void BindSpecparamsOf(const ModuleDecl& mod) {
    run_mgr->BindDesignSpecparams(CollectDeclaredSpecparams(mod), f.ctx,
                                  f.arena);
  }

  const PathDelay* PathOf(std::string_view prefix, std::string_view dst) const {
    for (const auto& pd : run_mgr->GetPathDelays()) {
      if (pd.inst_prefix == prefix && pd.dst_port == dst) return &pd;
    }
    return nullptr;
  }

  const TimingCheckEntry* Check(TimingCheckKind kind) const {
    for (const auto& tc : run_mgr->GetTimingChecks()) {
      if (tc.kind == kind) return &tc;
    }
    return nullptr;
  }

  uint64_t Specparam(std::string_view name) const {
    for (const auto& sp : run_mgr->GetSpecparamValues()) {
      if (sp.name == name) return sp.value;
    }
    return 0;
  }
};

std::string WriteSdf(const std::string& name, const std::string& text) {
  const std::string kPath = std::string("/tmp/delta_c32_06_") + name;
  std::ofstream out(kPath, std::ios::trunc);
  out << text;
  out.close();
  return kPath;
}

const char* const kIopathCell =
    "module iopath_leaf(input in_a, output out_z);\n"
    "  specify\n"
    "    (in_a => out_z) = 0;\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kOneInstance =
    "  logic first_z;\n"
    "  iopath_leaf a(1'b0, first_z);\n";

const char* const kTwoInstances =
    "  logic first_z;\n"
    "  logic second_z;\n"
    "  iopath_leaf a(1'b0, first_z);\n"
    "  iopath_leaf b(1'b0, second_z);\n";

std::string CellDesign(const std::string& instances, const std::string& calls) {
  return std::string(kIopathCell) + "module top;\n" + instances +
         "  initial begin\n" + calls + "  end\nendmodule\n";
}

std::string Call(const std::string& file) {
  return "    $sdf_annotate(\"" + file + "\");\n";
}

std::string CallInScope(const std::string& file, const std::string& scope) {
  return "    $sdf_annotate(\"" + file + "\", " + scope + ");\n";
}

std::string IopathRecord(const std::string& inst, const std::string& section,
                         const std::string& value) {
  return " (CELL (CELLTYPE \"iopath_leaf\") (INSTANCE top/" + inst +
         ") (DELAY (" + section + " (IOPATH in_a out_z (" + value + ")))))";
}

std::string DelayFile(const std::string& records) {
  return "(DELAYFILE" + records + ")";
}

TEST(SdfMultipleFiles, EachCallAnnotatesTheDesignFromItsOwnFile) {
  const std::string kF1 =
      WriteSdf("each_1.sdf", DelayFile(IopathRecord("a", "ABSOLUTE", "10")));
  const std::string kF2 =
      WriteSdf("each_2.sdf", DelayFile(IopathRecord("b", "ABSOLUTE", "20")));

  Annotated d;
  ASSERT_TRUE(d.Build(CellDesign(kTwoInstances, Call(kF1) + Call(kF2))));
  d.Run();

  const PathDelay* first = d.PathOf("a.", "out_z");
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(first->delays[0], 10u);
  const PathDelay* second = d.PathOf("b.", "out_z");
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(second->delays[0], 20u);
}

TEST(SdfMultipleFiles, AbsoluteValueOverwritesWhatAnEarlierFileAnnotated) {
  const std::string kF1 =
      WriteSdf("abs_1.sdf", DelayFile(IopathRecord("a", "ABSOLUTE", "5")));
  const std::string kF2 =
      WriteSdf("abs_2.sdf", DelayFile(IopathRecord("a", "ABSOLUTE", "9")));

  Annotated d;
  ASSERT_TRUE(d.Build(CellDesign(kOneInstance, Call(kF1) + Call(kF2))));
  d.Run();

  const PathDelay* path = d.PathOf("a.", "out_z");
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 9u);
}

TEST(SdfMultipleFiles, IncrementValueModifiesWhatAnEarlierFileAnnotated) {
  const std::string kF1 =
      WriteSdf("inc_1.sdf", DelayFile(IopathRecord("a", "ABSOLUTE", "5")));
  const std::string kF2 =
      WriteSdf("inc_2.sdf", DelayFile(IopathRecord("a", "INCREMENT", "3")));

  Annotated d;
  ASSERT_TRUE(d.Build(CellDesign(kOneInstance, Call(kF1) + Call(kF2))));
  d.Run();

  const PathDelay* path = d.PathOf("a.", "out_z");
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 8u);
}

TEST(SdfMultipleFiles, RepeatingOneIncrementFileModifiesTheDesignEachTime) {
  const std::string kF1 =
      WriteSdf("rep_1.sdf", DelayFile(IopathRecord("a", "ABSOLUTE", "5")));
  const std::string kF2 =
      WriteSdf("rep_2.sdf", DelayFile(IopathRecord("a", "INCREMENT", "3")));

  Annotated d;
  ASSERT_TRUE(
      d.Build(CellDesign(kOneInstance, Call(kF1) + Call(kF2) + Call(kF2))));
  d.Run();

  const PathDelay* path = d.PathOf("a.", "out_z");
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 11u);
}

TEST(SdfMultipleFiles,
     SecondArgumentAnnotatesDifferentRegionsFromDifferentFiles) {
  const std::string kF1 =
      WriteSdf("region_1.sdf", DelayFile(IopathRecord("a", "ABSOLUTE", "10") +
                                         IopathRecord("b", "ABSOLUTE", "11")));
  const std::string kF2 =
      WriteSdf("region_2.sdf", DelayFile(IopathRecord("a", "ABSOLUTE", "20") +
                                         IopathRecord("b", "ABSOLUTE", "21")));

  Annotated d;
  ASSERT_TRUE(d.Build(CellDesign(
      kTwoInstances, CallInScope(kF1, "top.a") + CallInScope(kF2, "top.b"))));
  d.Run();

  const PathDelay* from_first = d.PathOf("a.", "out_z");
  ASSERT_NE(from_first, nullptr);
  EXPECT_EQ(from_first->delays[0], 10u);
  const PathDelay* from_second = d.PathOf("b.", "out_z");
  ASSERT_NE(from_second, nullptr);
  EXPECT_EQ(from_second->delays[0], 21u);
}

TEST(SdfMultipleFiles, IncrementInALaterFileReachesOnlyTheRegionItNames) {
  const std::string kF1 = WriteSdf(
      "regioninc_1.sdf", DelayFile(IopathRecord("a", "ABSOLUTE", "4") +
                                   IopathRecord("b", "ABSOLUTE", "4")));
  const std::string kF2 = WriteSdf(
      "regioninc_2.sdf", DelayFile(IopathRecord("a", "INCREMENT", "6") +
                                   IopathRecord("b", "INCREMENT", "6")));

  Annotated d;
  ASSERT_TRUE(d.Build(
      CellDesign(kTwoInstances, Call(kF1) + CallInScope(kF2, "top.a"))));
  d.Run();

  const PathDelay* incremented = d.PathOf("a.", "out_z");
  ASSERT_NE(incremented, nullptr);
  EXPECT_EQ(incremented->delays[0], 10u);
  const PathDelay* untouched = d.PathOf("b.", "out_z");
  ASSERT_NE(untouched, nullptr);
  EXPECT_EQ(untouched->delays[0], 4u);
}

std::string CheckDesign(const std::string& calls) {
  return "module check_leaf(input d_in, input clk_in, output q_out);\n"
         "  specify\n"
         "    $setup(d_in, posedge clk_in, 5);\n"
         "  endspecify\n"
         "endmodule\n"
         "module top;\n"
         "  logic q_wire;\n"
         "  check_leaf a(1'b0, 1'b0, q_wire);\n"
         "  initial begin\n" +
         calls + "  end\nendmodule\n";
}

std::string CheckRecord(const std::string& limit) {
  return "(DELAYFILE (CELL (CELLTYPE \"check_leaf\") (INSTANCE top/a)"
         " (TIMINGCHECK (SETUP d_in (posedge clk_in) (" +
         limit + ")))))";
}

TEST(SdfMultipleFiles, AbsoluteValueOverwritesAConstraintFromAnEarlierFile) {
  const std::string kF1 = WriteSdf("check_1.sdf", CheckRecord("12"));
  const std::string kF2 = WriteSdf("check_2.sdf", CheckRecord("30"));

  Annotated d;
  ASSERT_TRUE(d.Build(CheckDesign(Call(kF1) + Call(kF2))));
  d.AddTimingChecksOf(d.Cell());
  ASSERT_NE(d.Check(TimingCheckKind::kSetup), nullptr);
  ASSERT_EQ(d.Check(TimingCheckKind::kSetup)->limit, 5u);

  d.Run();

  EXPECT_EQ(d.Check(TimingCheckKind::kSetup)->limit, 30u);
}

std::string SpecparamDesign(const std::string& calls) {
  return "module top(input a_in, output z_out);\n"
         "  specify\n"
         "    specparam cap = 4;\n"
         "    (a_in => z_out) = cap;\n"
         "  endspecify\n"
         "  initial begin\n" +
         calls + "  end\nendmodule\n";
}

std::string LabelRecord(const std::string& section, const std::string& value) {
  return "(DELAYFILE (CELL (CELLTYPE \"top\") (INSTANCE top) (LABEL (" +
         section + " (cap " + value + ")))))";
}

TEST(SdfMultipleFiles, IncrementModifiesASpecparamFromAnEarlierFile) {
  const std::string kF1 =
      WriteSdf("label_1.sdf", LabelRecord("ABSOLUTE", "20"));
  const std::string kF2 =
      WriteSdf("label_2.sdf", LabelRecord("INCREMENT", "7"));

  Annotated d;
  ASSERT_TRUE(d.Build(SpecparamDesign(Call(kF1) + Call(kF2))));
  d.BindSpecparamsOf(d.Top());
  const PathDelay* declared = d.PathOf("", "z_out");
  ASSERT_NE(declared, nullptr);
  ASSERT_EQ(declared->delays[0], 4u);

  d.Run();

  EXPECT_EQ(d.Specparam("cap"), 27u);
  const PathDelay* annotated = d.PathOf("", "z_out");
  ASSERT_NE(annotated, nullptr);
  EXPECT_EQ(annotated->delays[0], 27u);
}

}  // namespace
