#include <gtest/gtest.h>

#include <fstream>
#include <ios>
#include <string>
#include <string_view>

#include "fixture_sdf_design.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

std::string SdfFileNamed(const std::string& stem, const std::string& text) {
  const std::string kPath = "/tmp/delta_c32_09d_" + stem + ".sdf";
  std::ofstream out(kPath, std::ios::trunc);
  out << text;
  out.close();
  return kPath;
}

std::string LeafCellEntry(const std::string& instance_path,
                          const std::string& entry) {
  return " (CELL (CELLTYPE \"delay_leaf\") (INSTANCE " + instance_path +
         ") (DELAY (ABSOLUTE " + entry + ")))";
}

std::string LeafCell(const std::string& instance_path,
                     const std::string& value) {
  return LeafCellEntry(instance_path, "(IOPATH pin_i pin_o (" + value + "))");
}

std::string PairDesign(const std::string& path_delay,
                       const std::string& operands) {
  return "module delay_leaf(input pin_i, output pin_o);\n"
         "  specify\n"
         "    (pin_i => pin_o) = " +
         path_delay +
         ";\n"
         "  endspecify\n"
         "endmodule\n"
         "module harness;\n"
         "  logic left_o;\n"
         "  logic right_o;\n"
         "  delay_leaf u_left(1'b0, left_o);\n"
         "  delay_leaf u_right(1'b0, right_o);\n"
         "  initial $sdf_annotate(" +
         operands +
         ");\n"
         "endmodule\n";
}

std::string NestedDesign(const std::string& operands) {
  return "module delay_leaf(input pin_i, output pin_o);\n"
         "  specify\n"
         "    (pin_i => pin_o) = 3;\n"
         "  endspecify\n"
         "endmodule\n"
         "module wrap_block(input w_i, output w_o);\n"
         "  delay_leaf u_inner(w_i, w_o);\n"
         "endmodule\n"
         "module harness;\n"
         "  logic deep_o;\n"
         "  wrap_block u_mid(1'b0, deep_o);\n"
         "  initial $sdf_annotate(" +
         operands +
         ");\n"
         "endmodule\n";
}

struct RunOfDesign {
  SdfDesign built;
  SpecifyManager* mgr = nullptr;

  bool Start(const std::string& src) {
    if (!built.Lower(src)) return false;
    mgr = built.f.ctx.GetSpecifyManager();
    if (mgr == nullptr) return false;
    built.f.scheduler.Run();
    return true;
  }

  const PathDelay* PathUnder(std::string_view prefix) const {
    for (const auto& pd : mgr->GetPathDelays()) {
      if (pd.inst_prefix == prefix && pd.dst_port == "pin_o") return &pd;
    }
    return nullptr;
  }
};

TEST(SdfPerInstanceIopath, TwoInstancesOfOneCellTakeTheirOwnIopathDelays) {
  const std::string kSdf =
      SdfFileNamed("apart", "(DELAYFILE" + LeafCell("harness/u_left", "17") +
                                LeafCell("harness/u_right", "29") + ")");

  RunOfDesign run;
  ASSERT_TRUE(run.Start(PairDesign("3", "\"" + kSdf + "\"")));

  const PathDelay* left = run.PathUnder("u_left.");
  ASSERT_NE(left, nullptr);
  EXPECT_EQ(left->delays[0], 17u);
  const PathDelay* right = run.PathUnder("u_right.");
  ASSERT_NE(right, nullptr);
  EXPECT_EQ(right->delays[0], 29u);
}

TEST(SdfPerInstanceIopath, ModuleInstanceOperandNarrowsToTheInstanceItNames) {
  const std::string kSdf =
      SdfFileNamed("narrowed", "(DELAYFILE" + LeafCell("harness/u_left", "11") +
                                   LeafCell("harness/u_right", "47") + ")");

  RunOfDesign run;
  ASSERT_TRUE(run.Start(PairDesign("3", "\"" + kSdf + "\", harness.u_left")));

  const PathDelay* named = run.PathUnder("u_left.");
  ASSERT_NE(named, nullptr);
  EXPECT_EQ(named->delays[0], 11u);
  const PathDelay* unnamed = run.PathUnder("u_right.");
  ASSERT_NE(unnamed, nullptr);
  EXPECT_EQ(unnamed->delays[0], 3u);
}

TEST(SdfPerInstanceIopath,
     SlashDividedInstancePathReachesADotSeparatedInstance) {
  const std::string kSdf = SdfFileNamed(
      "dividers", "(DELAYFILE" + LeafCell("harness/u_mid/u_inner", "23") + ")");

  RunOfDesign run;
  ASSERT_TRUE(run.Start(NestedDesign("\"" + kSdf + "\"")));

  const PathDelay* nested = run.PathUnder("u_mid.u_inner.");
  ASSERT_NE(nested, nullptr);
  EXPECT_EQ(nested->delays[0], 23u);
}

TEST(SdfPerInstanceIopath, TwoInstancesOfOneCellTakeTheirOwnPathpulseLimits) {
  const std::string kSdf = SdfFileNamed(
      "pulse",
      "(DELAYFILE" +
          LeafCellEntry("harness/u_left", "(PATHPULSE pin_i pin_o (37))") +
          LeafCellEntry("harness/u_right", "(PATHPULSE pin_i pin_o (53))") +
          ")");

  RunOfDesign run;
  ASSERT_TRUE(run.Start(PairDesign("90", "\"" + kSdf + "\"")));

  const PathDelay* left = run.PathUnder("u_left.");
  ASSERT_NE(left, nullptr);
  EXPECT_EQ(left->reject_limit[0], 37u);
  EXPECT_EQ(left->error_limit[0], 37u);
  const PathDelay* right = run.PathUnder("u_right.");
  ASSERT_NE(right, nullptr);
  EXPECT_EQ(right->reject_limit[0], 53u);
  EXPECT_EQ(right->error_limit[0], 53u);
}

TEST(SdfPerInstanceIopath, TwoInstancesOfOneCellTakeTheirOwnDeviceDelays) {
  const std::string kSdf = SdfFileNamed(
      "device",
      "(DELAYFILE" + LeafCellEntry("harness/u_left", "(DEVICE pin_o (41))") +
          LeafCellEntry("harness/u_right", "(DEVICE pin_o (59))") + ")");

  RunOfDesign run;
  ASSERT_TRUE(run.Start(PairDesign("3", "\"" + kSdf + "\"")));

  const PathDelay* left = run.PathUnder("u_left.");
  ASSERT_NE(left, nullptr);
  EXPECT_EQ(left->delays[0], 41u);
  const PathDelay* right = run.PathUnder("u_right.");
  ASSERT_NE(right, nullptr);
  EXPECT_EQ(right->delays[0], 59u);
}

TEST(SdfPerInstanceIopath, CellPathThroughAGenerateBlockReachesItsInstance) {
  const std::string kSdf = SdfFileNamed(
      "generate", "(DELAYFILE" + LeafCell("harness/gb/u", "19") + ")");

  RunOfDesign run;
  ASSERT_TRUE(
      run.Start("module delay_leaf(input pin_i, output pin_o);\n"
                "  specify\n"
                "    (pin_i => pin_o) = 3;\n"
                "  endspecify\n"
                "endmodule\n"
                "module harness;\n"
                "  logic gen_o;\n"
                "  if (1) begin : gb\n"
                "    delay_leaf u(1'b0, gen_o);\n"
                "  end\n"
                "  initial $sdf_annotate(\"" +
                kSdf +
                "\");\n"
                "endmodule\n"));

  const PathDelay* path = run.PathUnder("gb_u.");
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 19u);
}

}  // namespace
