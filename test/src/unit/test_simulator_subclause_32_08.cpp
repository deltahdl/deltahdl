#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_sdf_design.h"
#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "parser/ast_module.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_sdf.h"

using namespace delta;

namespace {

bool BuildDesign(const std::string& src, SimFixture& f, SpecifyManager& mgr) {
  auto* cu = RunModuleSource(src, f);
  if (cu == nullptr) return false;
  const ModuleDecl& mod = *cu->modules.back();
  RegisterPrimitiveDrivers(mod, f, mgr);
  RegisterPathDelays(mod, f, mgr);
  return true;
}

void AnnotateFileOnto(const std::string& sdf, SpecifyManager& mgr,
                      SdfMtm mtm = SdfMtm::kTypical) {
  SdfFile file;
  EXPECT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, mtm);
}

std::string DelaySdf(const std::string& entries) {
  return "(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1) (DELAY (ABSOLUTE " +
         entries + ")))) ";
}

std::string IncrementDelaySdf(const std::string& entries) {
  return "(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1) (DELAY (INCREMENT " +
         entries + ")))) ";
}

std::string TopDelaySdf(const std::string& entries) {
  const std::string kHead =
      "(DELAYFILE (CELL (CELLTYPE \"top\") (INSTANCE top) (DELAY (ABSOLUTE ";
  return kHead + entries + ")))) ";
}

const char* const kPathDesign =
    "module t(input a, output y);\n"
    "  specify\n"
    "    (a => y) = (11, 12, 13, 14, 15, 16);\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kGateDesign =
    "module t(input a, input en, output y);\n"
    "  bufif1 #(1, 2, 3) g1(y, a, en);\n"
    "endmodule\n";

const char* const kInterconnectDesign =
    "module drv(q);\n"
    "  output q;\n"
    "  reg q;\n"
    "endmodule\n"
    "module ld(d);\n"
    "  input d;\n"
    "  wire d;\n"
    "endmodule\n"
    "module top;\n"
    "  wire n;\n"
    "  drv u1(.q(n));\n"
    "  ld u2(.d(n));\n"
    "endmodule\n";

bool BuildInterconnectDesign(SdfDesign& d) {
  if (!d.Lower(kInterconnectDesign)) return false;
  d.mgr.BindDesignInterconnect(CollectInterconnectTopology(*d.cu, d.Top()));
  return true;
}

const PathDelay* PathAToY(const SpecifyManager& mgr) {
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == "a" && pd.dst_port == "y") return &pd;
  }
  return nullptr;
}

const PrimitiveDriver* DriverOfY(const SpecifyManager& mgr) {
  for (const auto& drv : mgr.GetPrimitiveDrivers()) {
    if (drv.output_port == "y") return &drv;
  }
  return nullptr;
}

const InterconnectDelay* LoadOfU2D(const SpecifyManager& mgr) {
  for (const auto& ic : mgr.GetInterconnectDelays()) {
    if (ic.dst_port == "u2/d") return &ic;
  }
  return nullptr;
}

constexpr int kTransitions = 12;

TEST(SdfTwelveTransitionMapping, OneIopathValueReachesEveryTransition) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));
  ASSERT_NE(PathAToY(mgr), nullptr);

  AnnotateFileOnto(DelaySdf("(IOPATH a y (5))"), mgr);

  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], 5u) << "transition slot " << i;
  }
}

TEST(SdfTwelveTransitionMapping, TwoIopathValuesKeepRiseAndFallFamiliesApart) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y (5) (9))"), mgr);

  const uint64_t kExpected[kTransitions] = {5, 9, 5, 5, 9, 9, 5, 5, 9, 9, 9, 5};
  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], kExpected[i]) << "transition slot " << i;
  }
}

TEST(SdfTwelveTransitionMapping, ThreeIopathValuesAddTheTurnOffFamily) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y (4) (6) (9))"), mgr);

  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 4u);
  EXPECT_EQ(pd->delays[1], 6u);
  EXPECT_EQ(pd->delays[2], 9u);
  EXPECT_EQ(pd->delays[3], 4u);
  EXPECT_EQ(pd->delays[4], 9u);
  EXPECT_EQ(pd->delays[5], 6u);
  EXPECT_EQ(pd->delays[6], 4u);
  EXPECT_EQ(pd->delays[7], 4u);
  EXPECT_EQ(pd->delays[8], 6u);
  EXPECT_EQ(pd->delays[9], 6u);
  EXPECT_EQ(pd->delays[10], 9u);
  EXPECT_EQ(pd->delays[11], 4u);
}

TEST(SdfTwelveTransitionMapping, SixIopathValuesDeriveTheXTransitions) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y (7) (3) (9) (2) (8) (4))"), mgr);

  const uint64_t kExpected[kTransitions] = {7, 3, 9, 2, 8, 4, 7, 7, 3, 4, 9, 2};
  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], kExpected[i]) << "transition slot " << i;
  }
}

TEST(SdfTwelveTransitionMapping, TwelveIopathValuesAreTakenAsWritten) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y (21) (22) (23) (24) (25) (26)"
                            " (27) (28) (29) (30) (31) (32))"),
                   mgr);

  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], static_cast<uint64_t>(21 + i))
        << "transition slot " << i;
  }
}

TEST(SdfTwelveTransitionMapping, MinTypMaxValuesSpreadTheirMinimumMember) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y (1:2:3) (4:5:6))"), mgr,
                   SdfMtm::kMinimum);

  const uint64_t kExpected[kTransitions] = {1, 4, 1, 1, 4, 4, 1, 1, 4, 4, 4, 1};
  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], kExpected[i]) << "transition slot " << i;
  }
}

TEST(SdfTwelveTransitionMapping, MinTypMaxValuesSpreadTheirTypicalMember) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y (1:2:3) (4:5:6))"), mgr,
                   SdfMtm::kTypical);

  const uint64_t kExpected[kTransitions] = {2, 5, 2, 2, 5, 5, 2, 2, 5, 5, 5, 2};
  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], kExpected[i]) << "transition slot " << i;
  }
}

TEST(SdfTwelveTransitionMapping, MinTypMaxValuesSpreadTheirMaximumMember) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y (1:2:3) (4:5:6))"), mgr,
                   SdfMtm::kMaximum);

  const uint64_t kExpected[kTransitions] = {3, 6, 3, 3, 6, 6, 3, 3, 6, 6, 6, 3};
  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], kExpected[i]) << "transition slot " << i;
  }
}

TEST(SdfTwelveTransitionMapping, OneExtendedDirectionReachesEveryTransition) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y ((6)))"), mgr);

  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], 6u) << "transition slot " << i;
  }
}

TEST(SdfTwelveTransitionMapping, TwoExtendedDirectionsKeepTheFamiliesApart) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y ((6) (2) (3)) ((8) (2) (3)))"), mgr);

  const uint64_t kExpected[kTransitions] = {6, 8, 6, 6, 8, 8, 6, 6, 8, 8, 8, 6};
  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], kExpected[i]) << "transition slot " << i;
  }
}

TEST(SdfTwelveTransitionMapping, SixInterconnectValuesDeriveTheXTransitions) {
  SdfDesign d;
  ASSERT_TRUE(BuildInterconnectDesign(d));

  AnnotateFileOnto(
      TopDelaySdf("(INTERCONNECT u1/q u2/d (7) (3) (9) (2) (8) (4))"), d.mgr);

  const uint64_t kExpected[kTransitions] = {7, 3, 9, 2, 8, 4, 7, 7, 3, 4, 9, 2};
  const InterconnectDelay* got = LoadOfU2D(d.mgr);
  ASSERT_NE(got, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(got->delays[i], kExpected[i]) << "transition slot " << i;
  }
}

TEST(SdfThreeTransitionMapping, MoreThanThreeDeviceValuesLoseTheExtras) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kGateDesign, f, mgr));
  ASSERT_NE(DriverOfY(mgr), nullptr);

  AnnotateFileOnto(DelaySdf("(DEVICE (30) (10) (20) (40) (50) (60))"), mgr);

  const PrimitiveDriver* drv = DriverOfY(mgr);
  ASSERT_NE(drv, nullptr);
  EXPECT_EQ(drv->delays[0], 30u);
  EXPECT_EQ(drv->delays[1], 10u);
  EXPECT_EQ(drv->delays[2], 20u);
  EXPECT_EQ(drv->delays[3], 30u);
  EXPECT_EQ(drv->delays[4], 20u);
  EXPECT_EQ(drv->delays[5], 10u);
  const uint64_t kDropped[3] = {40, 50, 60};
  for (uint64_t dropped : kDropped) {
    for (int i = 0; i < kTransitions; ++i) {
      EXPECT_NE(drv->delays[i], dropped) << "slot " << i << " has " << dropped;
    }
  }
}

TEST(SdfThreeTransitionMapping, DeviceDelayToTheXStateIsTheSmallestOfThree) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kGateDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(DEVICE (30) (10) (20) (40) (50) (60))"), mgr);

  const PrimitiveDriver* drv = DriverOfY(mgr);
  ASSERT_NE(drv, nullptr);
  EXPECT_EQ(drv->delays[6], 10u);
  EXPECT_EQ(drv->delays[8], 10u);
  EXPECT_EQ(drv->delays[11], 10u);
}

TEST(SdfThreeTransitionMapping, TwoDeviceValuesTurnOffAtTheSmaller) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kGateDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(DEVICE (5) (3))"), mgr);

  const PrimitiveDriver* drv = DriverOfY(mgr);
  ASSERT_NE(drv, nullptr);
  EXPECT_EQ(drv->delays[2], 3u);
  EXPECT_EQ(drv->delays[4], 3u);
  EXPECT_EQ(drv->delays[10], 3u);
}

TEST(SdfThreeTransitionMapping, EmptyDeviceValueHoldsTheDeclaredDelay) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kGateDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(DEVICE () (7))"), mgr);

  const PrimitiveDriver* drv = DriverOfY(mgr);
  ASSERT_NE(drv, nullptr);
  EXPECT_EQ(drv->delays[0], 1u);
  EXPECT_EQ(drv->delays[1], 7u);
}

TEST(SdfThreeTransitionMapping, IncrementDeviceAddsOnlyTheThreeItKept) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kGateDesign, f, mgr));
  const PrimitiveDriver* before = DriverOfY(mgr);
  ASSERT_NE(before, nullptr);
  ASSERT_EQ(before->delays[3], 1u);

  AnnotateFileOnto(IncrementDelaySdf("(DEVICE (30) (10) (20) (40) (50) (60))"),
                   mgr);

  const PrimitiveDriver* drv = DriverOfY(mgr);
  ASSERT_NE(drv, nullptr);
  EXPECT_EQ(drv->delays[0], 31u);
  EXPECT_EQ(drv->delays[1], 12u);
  EXPECT_EQ(drv->delays[2], 23u);
  EXPECT_EQ(drv->delays[3], 31u);
  EXPECT_EQ(drv->delays[4], 23u);
  EXPECT_EQ(drv->delays[5], 12u);
}

TEST(SdfThreeTransitionMapping, IncrementDeviceRaisesTheXDelayByTheSmallest) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kGateDesign, f, mgr));
  const PrimitiveDriver* before = DriverOfY(mgr);
  ASSERT_NE(before, nullptr);
  ASSERT_EQ(before->delays[6], 1u);

  AnnotateFileOnto(IncrementDelaySdf("(DEVICE (30) (10) (20) (40) (50) (60))"),
                   mgr);

  const PrimitiveDriver* drv = DriverOfY(mgr);
  ASSERT_NE(drv, nullptr);
  EXPECT_EQ(drv->delays[6], 11u);
  EXPECT_EQ(drv->delays[8], 11u);
  EXPECT_EQ(drv->delays[11], 11u);
}

TEST(SdfThreeTransitionMapping, DeviceOnASpecifyPathKeepsAllTwelve) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(DEVICE (30) (10) (20) (40) (50) (60))"), mgr);

  const uint64_t kExpected[kTransitions] = {30, 10, 20, 40, 50, 60,
                                            20, 40, 10, 60, 50, 40};
  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], kExpected[i]) << "transition slot " << i;
  }
}

}  // namespace
