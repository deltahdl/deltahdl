#pragma once

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
