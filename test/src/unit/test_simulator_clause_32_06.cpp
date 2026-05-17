#include <gtest/gtest.h>

#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

TEST(SdfMultipleFiles, SecondAbsoluteFileOverwritesFirstFilesPathDelay) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  mgr.AddPathDelay(pre);

  SdfFile first;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20))))))
  )", first));
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (50) (80))))))
  )", second));
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 50u);
  EXPECT_EQ(pd.delays[1], 80u);
}

TEST(SdfMultipleFiles, SecondFilePreservesUntouchedAnnotationsFromFirst) {
  SpecifyManager mgr;
  PathDelay a;
  a.src_port = "A";
  a.dst_port = "Z";
  a.delay_count = 1;
  a.delays[0] = 1;
  mgr.AddPathDelay(a);
  PathDelay b;
  b.src_port = "B";
  b.dst_port = "Y";
  b.delay_count = 1;
  b.delays[0] = 1;
  mgr.AddPathDelay(b);

  SdfFile first;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20))))))
  )", first));
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH B Y (40) (60))))))
  )", second));
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 2u);
  bool saw_first = false;
  bool saw_second = false;
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == "A" && pd.dst_port == "Z") {
      EXPECT_EQ(pd.delays[0], 10u);
      EXPECT_EQ(pd.delays[1], 20u);
      saw_first = true;
    } else if (pd.src_port == "B" && pd.dst_port == "Y") {
      EXPECT_EQ(pd.delays[0], 40u);
      EXPECT_EQ(pd.delays[1], 60u);
      saw_second = true;
    }
  }
  EXPECT_TRUE(saw_first);
  EXPECT_TRUE(saw_second);
}

TEST(SdfMultipleFiles, IncrementFromSecondFileAddsToFirstFilesPathDelay) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  mgr.AddPathDelay(pre);

  SdfFile first;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20))))))
  )", first));
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (INCREMENT (IOPATH A Z (5) (3))))))
  )", second));
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 15u);
  EXPECT_EQ(pd.delays[1], 23u);
}

TEST(SdfMultipleFiles, AbsoluteAfterIncrementWipesAccumulatedValue) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  mgr.AddPathDelay(pre);

  SdfFile first;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20))))))
  )", first));
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (INCREMENT (IOPATH A Z (5) (3))))))
  )", second));
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  SdfFile third;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (50) (80))))))
  )", third));
  AnnotateSdfToManager(third, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 50u);
  EXPECT_EQ(pd.delays[1], 80u);
}

TEST(SdfMultipleFiles,
     SecondAbsoluteFileOverwritesFirstFilesInterconnectDelay) {
  SpecifyManager mgr;

  SdfFile first;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (INTERCONNECT s d (5))))))
  )", first));
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (INTERCONNECT s d (8))))))
  )", second));
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  const auto& ic = mgr.GetInterconnectDelays()[0];
  EXPECT_EQ(ic.src_port, "s");
  EXPECT_EQ(ic.dst_port, "d");
  EXPECT_EQ(ic.rise, 8u);
}

TEST(SdfMultipleFiles,
     IncrementFromSecondFileAddsToFirstFilesInterconnectDelay) {
  SpecifyManager mgr;

  SdfFile first;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (INTERCONNECT s d (5) (7))))))
  )", first));
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (INCREMENT (INTERCONNECT s d (2) (3))))))
  )", second));
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  const auto& ic = mgr.GetInterconnectDelays()[0];
  EXPECT_EQ(ic.src_port, "s");
  EXPECT_EQ(ic.dst_port, "d");
  EXPECT_EQ(ic.rise, 7u);
  EXPECT_EQ(ic.fall, 10u);
}

TEST(SdfMultipleFiles, ScopeFilterSkipsCellsOutsideHierarchyScope) {
  SpecifyManager mgr;

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1/dut)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20)))))
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u2/dut)
        (DELAY (ABSOLUTE (IOPATH B Y (40) (60))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical, "u1");

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.src_port, "A");
  EXPECT_EQ(pd.dst_port, "Z");
  EXPECT_EQ(pd.delays[0], 10u);
  EXPECT_EQ(pd.delays[1], 20u);
}

TEST(SdfMultipleFiles,
     ScopeFilterAnnotatesCellsHierarchicallyUnderTheScope) {
  SpecifyManager mgr;

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1/sub/dut)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical, "u1");

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 10u);
  EXPECT_EQ(pd.delays[1], 20u);
}

TEST(SdfMultipleFiles, ScopeFilterAnnotatesCellWhenInstanceEqualsScope) {
  SpecifyManager mgr;

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical, "u1");

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 10u);
  EXPECT_EQ(pd.delays[1], 20u);
}

TEST(SdfMultipleFiles, EmptyScopeAnnotatesEveryCell) {
  SpecifyManager mgr;

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1/dut)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20)))))
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u2/dut)
        (DELAY (ABSOLUTE (IOPATH B Y (40) (60))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 2u);
}

TEST(SdfMultipleFiles, ScopeFilterDoesNotMatchSiblingsWithSharedPrefix) {
  SpecifyManager mgr;

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u10/dut)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical, "u1");

  EXPECT_EQ(mgr.GetPathDelays().size(), 0u);
}

TEST(SdfMultipleFiles,
     TwoCallsWithDifferentScopesAnnotateDifferentRegions) {
  SpecifyManager mgr;

  SdfFile file_a;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1/dut)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20)))))
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u2/dut)
        (DELAY (ABSOLUTE (IOPATH B Y (40) (60))))))
  )", file_a));
  AnnotateSdfToManager(file_a, mgr, SdfMtm::kTypical, "u1");

  SdfFile file_b;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1/dut)
        (DELAY (ABSOLUTE (IOPATH A Z (99) (99)))))
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u2/dut)
        (DELAY (ABSOLUTE (IOPATH B Y (40) (60))))))
  )", file_b));
  AnnotateSdfToManager(file_b, mgr, SdfMtm::kTypical, "u2");

  ASSERT_EQ(mgr.GetPathDelays().size(), 2u);
  bool saw_a = false;
  bool saw_b = false;
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == "A" && pd.dst_port == "Z") {
      EXPECT_EQ(pd.delays[0], 10u);
      EXPECT_EQ(pd.delays[1], 20u);
      saw_a = true;
    } else if (pd.src_port == "B" && pd.dst_port == "Y") {
      EXPECT_EQ(pd.delays[0], 40u);
      EXPECT_EQ(pd.delays[1], 60u);
      saw_b = true;
    }
  }
  EXPECT_TRUE(saw_a);
  EXPECT_TRUE(saw_b);
}

TEST(SdfMultipleFiles,
     SecondAbsoluteFileOverwritesFirstFilesSpecparamValue) {
  SpecifyManager mgr;

  SdfFile first;
  {
    SdfCell cell;
    SdfSpecparam sp;
    sp.name = "tHold";
    sp.value.typ_val = 11;
    cell.specparams.push_back(sp);
    first.cells.push_back(cell);
  }
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  {
    SdfCell cell;
    SdfSpecparam sp;
    sp.name = "tHold";
    sp.value.typ_val = 47;
    cell.specparams.push_back(sp);
    second.cells.push_back(cell);
  }
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetSpecparamValues().size(), 1u);
  EXPECT_EQ(mgr.GetSpecparamValues()[0].value, 47u);
}

TEST(SdfMultipleFiles,
     SecondAbsoluteFileOverwritesFirstFilesConditionalPathDelay) {
  SpecifyManager mgr;
  PathDelay sv;
  sv.src_port = "a";
  sv.dst_port = "y";
  sv.condition = "mode";
  sv.delay_count = 1;
  sv.delays[0] = 0;
  mgr.AddPathDelay(sv);

  SdfFile first;
  {
    SdfCell cell;
    SdfIopath io;
    io.src_port = "a";
    io.dst_port = "y";
    io.condition = "mode";
    io.rise.typ_val = 11;
    io.fall.typ_val = 22;
    cell.iopaths.push_back(io);
    first.cells.push_back(cell);
  }
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  {
    SdfCell cell;
    SdfIopath io;
    io.src_port = "a";
    io.dst_port = "y";
    io.condition = "mode";
    io.rise.typ_val = 33;
    io.fall.typ_val = 44;
    cell.iopaths.push_back(io);
    second.cells.push_back(cell);
  }
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  EXPECT_EQ(mgr.GetPathDelays()[0].condition, "mode");
  EXPECT_EQ(mgr.GetPathDelays()[0].delays[0], 33u);
  EXPECT_EQ(mgr.GetPathDelays()[0].delays[1], 44u);
}

TEST(SdfMultipleFiles, ChainedIncrementCallsAccumulateOntoPathDelay) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  mgr.AddPathDelay(pre);

  SdfFile first;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20))))))
  )", first));
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (INCREMENT (IOPATH A Z (3) (5))))))
  )", second));
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  SdfFile third;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (INCREMENT (IOPATH A Z (4) (7))))))
  )", third));
  AnnotateSdfToManager(third, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];

  EXPECT_EQ(pd.delays[0], 17u);
  EXPECT_EQ(pd.delays[1], 32u);
}

TEST(SdfMultipleFiles, ScopeFilterAlsoSkipsInterconnectsFromOutOfScopeCells) {
  SpecifyManager mgr;

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1/dut)
        (DELAY (ABSOLUTE (INTERCONNECT s1 d1 (5)))))
      (CELL
        (CELLTYPE "net")
        (INSTANCE u2/dut)
        (DELAY (ABSOLUTE (INTERCONNECT s2 d2 (8))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical, "u1");

  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  const auto& ic = mgr.GetInterconnectDelays()[0];
  EXPECT_EQ(ic.src_port, "s1");
  EXPECT_EQ(ic.dst_port, "d1");
  EXPECT_EQ(ic.rise, 5u);
}

TEST(SdfMultipleFiles, ScopeFilterAlsoSkipsSpecparamsFromOutOfScopeCells) {
  SpecifyManager mgr;

  SdfFile file;
  {
    SdfCell cell;
    cell.instance = "u1/dut";
    SdfSpecparam sp;
    sp.name = "tHoldKept";
    sp.value.typ_val = 11;
    cell.specparams.push_back(sp);
    file.cells.push_back(cell);
  }
  {
    SdfCell cell;
    cell.instance = "u2/dut";
    SdfSpecparam sp;
    sp.name = "tHoldDropped";
    sp.value.typ_val = 99;
    cell.specparams.push_back(sp);
    file.cells.push_back(cell);
  }
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical, "u1");

  ASSERT_EQ(mgr.GetSpecparamValues().size(), 1u);
  EXPECT_EQ(mgr.GetSpecparamValues()[0].name, "tHoldKept");
  EXPECT_EQ(mgr.GetSpecparamValues()[0].value, 11u);
}

TEST(SdfMultipleFiles,
     IncrementFromSecondFileAddsToFirstFilesSpecparamValue) {
  SpecifyManager mgr;

  SdfFile first;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (LABEL (ABSOLUTE (tHold 11)))))
  )", first));
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (LABEL (INCREMENT (tHold 7)))))
  )", second));
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetSpecparamValues().size(), 1u);
  EXPECT_EQ(mgr.GetSpecparamValues()[0].name, "tHold");
  EXPECT_EQ(mgr.GetSpecparamValues()[0].value, 18u);
}

}
