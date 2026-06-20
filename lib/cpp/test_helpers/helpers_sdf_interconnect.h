#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

// Builds an SDF file containing a single cell with one INTERCONNECT delay
// entry (rise/fall typ values) and annotates it into the given manager using
// the supplied min/typ/max selection. The annotated delays remain owned by
// `mgr`, so callers keep `mgr` alive while inspecting GetInterconnectDelays().
inline void AnnotateSingleInterconnect(SpecifyManager& mgr,
                                       const std::string& src_port,
                                       const std::string& dst_port,
                                       uint64_t rise_typ, uint64_t fall_typ,
                                       SdfMtm mtm = SdfMtm::kTypical) {
  SdfFile file;
  SdfCell cell;
  SdfInterconnect ic;
  ic.kind = SdfInterconnectKind::kInterconnect;
  ic.src_port = src_port;
  ic.dst_port = dst_port;
  ic.rise.typ_val = rise_typ;
  ic.fall.typ_val = fall_typ;
  cell.interconnects.push_back(ic);
  file.cells.push_back(cell);

  AnnotateSdfToManager(file, mgr, mtm);
}

// Annotates a single two-value INTERCONNECT (src->dst, rise/fall) into `mgr`
// and asserts that exactly one interconnect delay results whose 12 transition
// slots match the Table 32-4 two-value expansion of (rise_typ, fall_typ).
inline void ExpectTwoValueInterconnectExpansion(SpecifyManager& mgr,
                                                const std::string& src_port,
                                                const std::string& dst_port,
                                                uint64_t rise_typ,
                                                uint64_t fall_typ) {
  AnnotateSingleInterconnect(mgr, src_port, dst_port, rise_typ, fall_typ);
  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  const auto& got = mgr.GetInterconnectDelays()[0];
  EXPECT_EQ(got.delays[0], rise_typ);
  EXPECT_EQ(got.delays[1], fall_typ);
  EXPECT_EQ(got.delays[2], rise_typ);
  EXPECT_EQ(got.delays[3], rise_typ);
  EXPECT_EQ(got.delays[4], fall_typ);
  EXPECT_EQ(got.delays[5], fall_typ);
  EXPECT_EQ(got.delays[6], rise_typ);
  EXPECT_EQ(got.delays[7], rise_typ);
  EXPECT_EQ(got.delays[8], fall_typ);
  EXPECT_EQ(got.delays[9], fall_typ);
  EXPECT_EQ(got.delays[10], fall_typ);
  EXPECT_EQ(got.delays[11], rise_typ);
}
