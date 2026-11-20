#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_sdf_design.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_sdf.h"

using namespace delta;

namespace {

struct OrderedRun : SdfDesign {
  bool Prepare(const std::string& src) {
    if (!Lower(src)) return false;
    mgr.BindDesignInterconnect(CollectInterconnectTopology(*cu, Top()));
    AddPathDelays(Top());
    return true;
  }

  void Apply(const std::string& sections) {
    SdfFile parsed;
    ASSERT_TRUE(ParseSdf(
        "(DELAYFILE (CELL (CELLTYPE \"c\") (INSTANCE u1) " + sections + "))",
        parsed));
    AnnotateSdfToManager(parsed, mgr, SdfMtm::kTypical);
  }

  const PathDelay* OnlyPath() const {
    const auto& paths = mgr.GetPathDelays();
    return paths.size() == 1 ? &paths.front() : nullptr;
  }

  const InterconnectDelay* Wire(std::string_view src,
                                std::string_view dst) const {
    return mgr.FindInterconnectDelay(src, dst);
  }
};

std::string Absolute(const std::string& entries) {
  return "(DELAY (ABSOLUTE " + entries + "))";
}

std::string Increment(const std::string& entries) {
  return "(DELAY (INCREMENT " + entries + "))";
}

const char* const kCellSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kZeroCellSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 0;\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kFanInSrc =
    "module src_cell(out);\n"
    "  output out;\n"
    "  reg out;\n"
    "endmodule\n"
    "module sink_cell(in);\n"
    "  input in;\n"
    "  wire in;\n"
    "endmodule\n"
    "module board;\n"
    "  wire n;\n"
    "  src_cell i13(.out(n));\n"
    "  src_cell i11(.out(n));\n"
    "  sink_cell i15(.in(n));\n"
    "endmodule\n";

const char* const kFanOutSrc =
    "module src_cell(out);\n"
    "  output out;\n"
    "  reg out;\n"
    "endmodule\n"
    "module sink_cell(in);\n"
    "  input in;\n"
    "  wire in;\n"
    "endmodule\n"
    "module board;\n"
    "  wire n;\n"
    "  src_cell i13(.out(n));\n"
    "  sink_cell i14(.in(n));\n"
    "  sink_cell i15(.in(n));\n"
    "endmodule\n";

TEST(SdfAnnotationOrder, IncrementPathpulseAddsToLimitsAnEarlierEntrySet) {
  OrderedRun run;
  ASSERT_TRUE(run.Prepare(kCellSrc));

  run.Apply(Absolute("(PATHPULSE A Z (21) (34))") +
            Increment("(PATHPULSE A Z (2) (3))"));

  const PathDelay* path = run.OnlyPath();
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 40u);
  EXPECT_EQ(path->reject_limit[0], 23u);
  EXPECT_EQ(path->error_limit[0], 37u);
}

TEST(SdfAnnotationOrder, IncrementDeviceAddsToAnEarlierDevice) {
  OrderedRun run;
  ASSERT_TRUE(run.Prepare(kCellSrc));

  run.Apply(Absolute("(DEVICE (7))") + Increment("(DEVICE (2))"));

  const PathDelay* path = run.OnlyPath();
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 9u);
}

TEST(SdfAnnotationOrder, IncrementDeviceAddsToAnEarlierIopath) {
  OrderedRun run;
  ASSERT_TRUE(run.Prepare(kCellSrc));

  run.Apply(Absolute("(IOPATH A Z (30))") + Increment("(DEVICE (2))"));

  const PathDelay* path = run.OnlyPath();
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 32u);
}

TEST(SdfAnnotationOrder, DeviceAfterIopathReplacesTheIopathValue) {
  OrderedRun run;
  ASSERT_TRUE(run.Prepare(kCellSrc));

  run.Apply(Absolute("(IOPATH A Z (30)) (DEVICE (7))"));

  const PathDelay* path = run.OnlyPath();
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 7u);
}

TEST(SdfAnnotationOrder, IopathAfterDeviceReplacesTheDeviceValue) {
  OrderedRun run;
  ASSERT_TRUE(run.Prepare(kCellSrc));

  run.Apply(Absolute("(DEVICE (7)) (IOPATH A Z (30))"));

  const PathDelay* path = run.OnlyPath();
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 30u);
}

TEST(SdfAnnotationOrder, IncrementNetdelayAddsToAnEarlierNetdelayOnThePort) {
  OrderedRun run;
  ASSERT_TRUE(run.Prepare(kFanInSrc));

  run.Apply(Absolute("(NETDELAY i15/in (5))") +
            Increment("(NETDELAY i15/in (3))"));

  for (const char* source : {"i13/out", "i11/out"}) {
    const InterconnectDelay* got = run.Wire(source, "i15/in");
    ASSERT_NE(got, nullptr) << source;
    EXPECT_EQ(got->delays[0], 8u) << source;
  }
}

TEST(SdfAnnotationOrder, IncrementNetdelayAddsToAnEarlierNetdelayOnTheNet) {
  OrderedRun run;
  ASSERT_TRUE(run.Prepare(kFanInSrc));

  run.Apply(Absolute("(NETDELAY n (5))") + Increment("(NETDELAY n (3))"));

  const InterconnectDelay* got = run.Wire("i13/out", "i15/in");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 8u);
}

TEST(SdfAnnotationOrder, IncrementNetdelayAddsToAnEarlierPort) {
  OrderedRun run;
  ASSERT_TRUE(run.Prepare(kFanInSrc));

  run.Apply(Absolute("(PORT i15/in (6))") + Increment("(NETDELAY i15/in (3))"));

  for (const char* source : {"i13/out", "i11/out"}) {
    const InterconnectDelay* got = run.Wire(source, "i15/in");
    ASSERT_NE(got, nullptr) << source;
    EXPECT_EQ(got->delays[0], 9u) << source;
  }
}

TEST(SdfAnnotationOrder,
     InterconnectToAnotherLoadAfterPortLeavesThePortedLoad) {
  OrderedRun run;
  ASSERT_TRUE(run.Prepare(kFanOutSrc));

  run.Apply(Absolute("(PORT i15/in (6)) (INTERCONNECT i13/out i14/in (5))"));

  const InterconnectDelay* ported = run.Wire("i13/out", "i15/in");
  ASSERT_NE(ported, nullptr);
  EXPECT_EQ(ported->delays[0], 6u);
  const InterconnectDelay* wired = run.Wire("i13/out", "i14/in");
  ASSERT_NE(wired, nullptr);
  EXPECT_EQ(wired->delays[0], 5u);
}

TEST(SdfEmptyValueHolds, HeldLimitsOnAZeroPathWithNoPulseLimitStayZero) {
  OrderedRun run;
  ASSERT_TRUE(run.Prepare(kZeroCellSrc));

  run.Apply(Absolute("(IOPATH A Z ((5) () ()))"));

  const PathDelay* path = run.OnlyPath();
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 5u);
  EXPECT_EQ(path->reject_limit[0], 0u);
  EXPECT_EQ(path->error_limit[0], 0u);
}

TEST(SdfEmptyValueHolds, EmptyPortValueHoldsTheDelayInForce) {
  OrderedRun run;
  ASSERT_TRUE(run.Prepare(kFanInSrc));

  run.Apply(Absolute("(PORT i15/in (6)) (PORT i15/in ())"));

  const InterconnectDelay* got = run.Wire("i11/out", "i15/in");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 6u);
}

TEST(SdfEmptyValueHolds, EmptyNetdelayValueHoldsTheDelayInForce) {
  OrderedRun run;
  ASSERT_TRUE(run.Prepare(kFanInSrc));

  run.Apply(Absolute("(PORT i15/in (6)) (NETDELAY i15/in ())"));

  const InterconnectDelay* got = run.Wire("i11/out", "i15/in");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 6u);
}

TEST(SdfEmptyValueHolds,
     DISABLED_InterconnectWithEmptyLimitFieldsHoldsTheLimits) {
  OrderedRun run;
  ASSERT_TRUE(run.Prepare(kFanInSrc));

  run.Apply(
      Absolute("(INTERCONNECT i13/out i15/in ((10) (4) (6)))"
               " (INTERCONNECT i13/out i15/in ((12) () ()))"));

  const InterconnectDelay* got = run.Wire("i13/out", "i15/in");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 12u);
  EXPECT_EQ(got->reject_limit[0], 4u);
  EXPECT_EQ(got->error_limit[0], 6u);
}

TEST(SdfEmptyValueHolds, DISABLED_PortWithEmptyLimitFieldsHoldsTheLimits) {
  OrderedRun run;
  ASSERT_TRUE(run.Prepare(kFanInSrc));

  run.Apply(
      Absolute("(PORT i15/in ((10) (4) (6))) (PORT i15/in ((12) () ()))"));

  const InterconnectDelay* got = run.Wire("i11/out", "i15/in");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 12u);
  EXPECT_EQ(got->reject_limit[0], 4u);
  EXPECT_EQ(got->error_limit[0], 6u);
}

}  // namespace
