#include <gtest/gtest.h>

#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

TEST(SdfInterconnectAnnotation, ParseInterconnectConstructCarriesSourceAndLoad) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (INTERCONNECT u2.q u3.d (4) (9))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells.size(), 1u);
  ASSERT_EQ(file.cells[0].interconnects.size(), 1u);
  const auto& ic = file.cells[0].interconnects[0];
  EXPECT_EQ(ic.kind, SdfInterconnectKind::kInterconnect);
  EXPECT_EQ(ic.src_port, "u2.q");
  EXPECT_EQ(ic.dst_port, "u3.d");
  EXPECT_EQ(ic.rise.typ_val, 4u);
  EXPECT_EQ(ic.fall.typ_val, 9u);
}

TEST(SdfInterconnectAnnotation, ParsePortConstructHasEmptySourceAndKindPort) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (PORT u3.d (5) (8))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells[0].interconnects.size(), 1u);
  const auto& ic = file.cells[0].interconnects[0];
  EXPECT_EQ(ic.kind, SdfInterconnectKind::kPort);
  EXPECT_TRUE(ic.src_port.empty());
  EXPECT_EQ(ic.dst_port, "u3.d");
  EXPECT_EQ(ic.rise.typ_val, 5u);
  EXPECT_EQ(ic.fall.typ_val, 8u);
}

TEST(SdfInterconnectAnnotation,
     ParseNetdelayConstructHasEmptySourceAndKindNetdelay) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (NETDELAY u3.d (6) (12))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells[0].interconnects.size(), 1u);
  const auto& ic = file.cells[0].interconnects[0];
  EXPECT_EQ(ic.kind, SdfInterconnectKind::kNetdelay);
  EXPECT_TRUE(ic.src_port.empty());
  EXPECT_EQ(ic.dst_port, "u3.d");
  EXPECT_EQ(ic.rise.typ_val, 6u);
  EXPECT_EQ(ic.fall.typ_val, 12u);
}

TEST(SdfInterconnectAnnotation, ConstructsDoNotProduceUnannotatableWarning) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (INTERCONNECT a.q b.d (1) (2))
          (PORT c.d (3) (4))
          (NETDELAY d.d (5) (6))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  SpecifyManager mgr;
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
  for (const auto& w : result.warnings) {
    EXPECT_EQ(w.find("INTERCONNECT"), std::string::npos) << w;
    EXPECT_EQ(w.find("PORT"), std::string::npos) << w;
    EXPECT_EQ(w.find("NETDELAY"), std::string::npos) << w;
  }
}

TEST(SdfInterconnectAnnotation, ParsedConstructsRouteToInterconnectDelays) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (INTERCONNECT a.q b.d (1) (2))
          (PORT c.d (3) (4))
          (NETDELAY d.d (5) (6))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
  const auto& ics = mgr.GetInterconnectDelays();
  ASSERT_EQ(ics.size(), 3u);
  EXPECT_EQ(ics[0].src_port, "a.q");
  EXPECT_EQ(ics[0].dst_port, "b.d");
  EXPECT_TRUE(ics[1].src_port.empty());
  EXPECT_EQ(ics[1].dst_port, "c.d");
  EXPECT_TRUE(ics[2].src_port.empty());
  EXPECT_EQ(ics[2].dst_port, "d.d");
}

// On a multisource net, an INTERCONNECT construct can carry a unique delay for
// each individual source/load pair. Two INTERCONNECT entries that share a load
// but name different sources are retained as distinct annotated delays (the
// per-(source,load) keying in AddInterconnectDelay).
TEST(SdfInterconnectAnnotation, MultipleSourcesToSameLoadCoexistAsDistinctEntries) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (INTERCONNECT s1.q load.d (3) (3))
          (INTERCONNECT s2.q load.d (7) (7))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
  const auto& ics = mgr.GetInterconnectDelays();
  ASSERT_EQ(ics.size(), 2u);
  EXPECT_EQ(ics[0].src_port, "s1.q");
  EXPECT_EQ(ics[0].dst_port, "load.d");
  EXPECT_EQ(ics[0].delays[0], 3u);
  EXPECT_EQ(ics[1].src_port, "s2.q");
  EXPECT_EQ(ics[1].dst_port, "load.d");
  EXPECT_EQ(ics[1].delays[0], 7u);
}

TEST(SdfInterconnectAnnotation, InterconnectDelayHas12TransitionSlots) {
  SdfFile file;
  SdfCell cell;
  SdfInterconnect ic;
  ic.kind = SdfInterconnectKind::kInterconnect;
  ic.src_port = "a";
  ic.dst_port = "b";
  ic.rise.typ_val = 7;
  ic.fall.typ_val = 11;
  cell.interconnects.push_back(ic);
  file.cells.push_back(cell);

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  const auto& got = mgr.GetInterconnectDelays()[0];

  EXPECT_EQ(got.delays[0], 7u);
  EXPECT_EQ(got.delays[1], 11u);
  EXPECT_EQ(got.delays[2], 7u);
  EXPECT_EQ(got.delays[3], 7u);
  EXPECT_EQ(got.delays[4], 11u);
  EXPECT_EQ(got.delays[5], 11u);
}

TEST(SdfInterconnectAnnotation, InterconnectPulseLimitsInitFromDelays) {
  SdfFile file;
  SdfCell cell;
  SdfInterconnect ic;
  ic.kind = SdfInterconnectKind::kInterconnect;
  ic.src_port = "a";
  ic.dst_port = "b";
  ic.rise.typ_val = 7;
  ic.fall.typ_val = 11;
  cell.interconnects.push_back(ic);
  file.cells.push_back(cell);

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
  const auto& got = mgr.GetInterconnectDelays()[0];
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(got.reject_limit[i], got.delays[i]) << "slot " << i;
    EXPECT_EQ(got.error_limit[i], got.delays[i]) << "slot " << i;
  }
}

// A PORT construct carries no source, so its delay represents the delay from
// all sources on the net to the load. Annotating it after source-specific
// INTERCONNECT entries to the same load collapses them into the single
// from-all-sources delay (the empty-source branch of AddInterconnectDelay).
TEST(SdfInterconnectAnnotation, PortDelayRepresentsAllSourcesReplacingPerSource) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (INTERCONNECT s1.q load.d (3) (3))
          (INTERCONNECT s2.q load.d (4) (4))
          (PORT load.d (9) (9))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
  const auto& ics = mgr.GetInterconnectDelays();
  ASSERT_EQ(ics.size(), 1u);
  EXPECT_TRUE(ics[0].src_port.empty());
  EXPECT_EQ(ics[0].dst_port, "load.d");
  EXPECT_EQ(ics[0].delays[0], 9u);
}

TEST(SdfInterconnectAnnotation, SingleValueDelayBroadcastsAcrossAllSlots) {
  SdfFile file;
  SdfCell cell;
  SdfInterconnect ic;
  ic.kind = SdfInterconnectKind::kInterconnect;
  ic.src_port = "a";
  ic.dst_port = "b";

  ic.rise.typ_val = 5;
  cell.interconnects.push_back(ic);
  file.cells.push_back(cell);

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
  const auto& got = mgr.GetInterconnectDelays()[0];
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(got.delays[i], 5u) << "slot " << i;
  }
}

}
