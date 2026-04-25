#include <gtest/gtest.h>

#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// =============================================================================
// §32.4.4 — SDF annotation of interconnect delays
// =============================================================================

// §32.4.4 Table 32-3 row "(INTERCONNECT...)": the construct names a source
// port followed by a load port and a delay list. The parser must decode
// both ports and surface them on the resulting SdfInterconnect so the
// downstream annotator can route the entry through the source/load
// matching rule the same paragraph spells out.
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

// §32.4.4 Table 32-3 row "(PORT...)": a PORT entry carries only the load
// port and the delay list — no source port — because the LRM defines its
// semantics as "the delay from all sources on the net to that port". The
// parser records this absence by leaving src_port empty and tagging the
// entry with kPort so a future stage can apply the "from all sources"
// fan-out rule.
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

// §32.4.4 Table 32-3 row "(NETDELAY...)" plus the paragraph naming its
// load-only shape: NETDELAY also carries no source port. The parser tags
// it with kNetdelay so a future stage can enforce the LRM's restriction
// that NETDELAY only land on input/inout module ports or on nets — a
// constraint the kPort fan-out path does not impose.
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

// §32.4.4 paragraph naming Table 32-3: the SDF parser must not silently
// drop INTERCONNECT/PORT/NETDELAY into the §32.3 unannotatable warning
// channel — they are explicitly mapped to interconnect delays in this
// clause, so backannotation owns them.
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

// §32.4.4 paragraph naming Table 32-3: the parsed entries must reach the
// SpecifyManager as InterconnectDelay records, preserving the load port
// (and source port when supplied) so a runtime that wires up references
// to the annotated load can find the matching delay.
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

// §32.4.4: "Interconnect delays have 12 transition delays". The runtime
// InterconnectDelay record must therefore expose a 12-slot transition
// table, mirroring the PathDelay shape, so per-transition lookups can
// resolve to the right delay value.
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
  // Two-value SDF expansion mirrors Table 32-4: rise covers 0->1/0->z/z->1
  // and fall covers 1->0/1->z/z->0 across the six non-x transition slots.
  EXPECT_EQ(got.delays[0], 7u);   // 0->1
  EXPECT_EQ(got.delays[1], 11u);  // 1->0
  EXPECT_EQ(got.delays[2], 7u);   // 0->z
  EXPECT_EQ(got.delays[3], 7u);   // z->1
  EXPECT_EQ(got.delays[4], 11u);  // 1->z
  EXPECT_EQ(got.delays[5], 11u);  // z->0
}

// §32.4.4: "unique reject and error pulse limits are associated with each
// of the 12" transition delays. The annotator must initialise per-slot
// reject/error limits to the corresponding transition delay so the
// default inertial-delay behaviour applies until a later mechanism
// revises them.
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

// §32.4.4: "The same rules for specify path delays for filling in missing
// delays … also apply for interconnect delays." A single-value SDF entry
// must therefore broadcast across every transition slot, exactly the
// fill behaviour Table 32-4 spells out for path delays.
TEST(SdfInterconnectAnnotation, SingleValueDelayBroadcastsAcrossAllSlots) {
  SdfFile file;
  SdfCell cell;
  SdfInterconnect ic;
  ic.kind = SdfInterconnectKind::kInterconnect;
  ic.src_port = "a";
  ic.dst_port = "b";
  // A "single-value" SDF entry leaves the fall delay at zero — only rise
  // is supplied. The fill rule should propagate the rise value into every
  // slot rather than leaving the unsupplied slots at zero.
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

}  // namespace
