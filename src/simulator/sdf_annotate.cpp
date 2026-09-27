// Which cells an $sdf_annotate call reaches and the order one cell's
// constructs are applied in. §32.9 has a module_instance operand name a level
// of the design hierarchy, and SdfCellPrefixInRegion reads each cell's
// instance path from that level down, keeping the cells at or below it and
// working out the instance prefix their entries carry, which is what holds an
// SDF record to the one module instance it names. §32.5 has annotation proceed
// in order, so AnnotateSdfCell walks a cell's constructs as the file wrote
// them, across its sections rather than within each, and AnnotateSdfCellEntry
// hands each construct to the function for its kind.
//
// Those six functions annotate the constructs of §32.4 and §32.7 and stand in
// simulator/sdf_annotate_entry.cpp, together with the §32.8 Table 32-4 delay
// expansion each of them reads. They are declared below rather than in
// simulator/sdf_parser.h because AnnotateSdfCellEntry is their only caller.

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/sdf_parser.h"

namespace delta {

// §32.4, §32.7: one SDF construct apiece, defined in
// simulator/sdf_annotate_entry.cpp.
void AnnotateSdfIopathEntry(const SdfIopath& io, std::string_view inst_prefix,
                            SpecifyManager& mgr, SdfMtm mtm);
void AnnotateSdfPulseLimitEntry(const SdfPulseLimit& pl,
                                std::string_view inst_prefix,
                                SpecifyManager& mgr, SdfMtm mtm);
void AnnotateSdfInterconnectEntry(const SdfInterconnect& ic,
                                  const SdfFile& file, SpecifyManager& mgr,
                                  SdfMtm mtm, SdfAnnotationResult& result);
void AnnotateSdfDeviceEntry(const SdfDevice& dev, std::string_view inst_prefix,
                            SpecifyManager& mgr, SdfMtm mtm,
                            SdfAnnotationResult& result);
void AnnotateSdfSpecparamEntry(const SdfSpecparam& sp,
                               std::string_view inst_prefix,
                               SpecifyManager& mgr, SdfMtm mtm);
void AnnotateSdfTimingCheckEntry(const SdfTimingCheck& tc,
                                 std::string_view inst_prefix,
                                 SpecifyManager& mgr, SdfMtm mtm,
                                 SdfAnnotationResult& result);

std::optional<std::string> SdfCellPrefixInRegion(std::string_view instance,
                                                 std::string_view region_prefix,
                                                 std::string_view design_root) {
  if (design_root.empty()) return std::string();
  std::string path(instance);
  for (char& divider : path) {
    if (divider == '/') divider = '.';
  }
  std::string prefix;
  if (path == design_root) {
    prefix.clear();
  } else if (path.size() > design_root.size() &&
             path.compare(0, design_root.size(), design_root) == 0 &&
             path[design_root.size()] == '.') {
    prefix = path.substr(design_root.size() + 1) + ".";
  } else {
    prefix = std::string(region_prefix);
    if (!path.empty()) prefix += path + ".";
  }
  if (prefix.compare(0, region_prefix.size(), region_prefix) != 0)
    return std::nullopt;
  return prefix;
}

namespace {

// Builds the implicit construct ordering used when a cell does not carry an
// explicit one, as a cell assembled in memory rather than parsed does not:
// all iopaths, then pulse limits, then interconnects, devices, specparams and
// timing checks.
std::vector<SdfCellEntryRef> BuildDerivedSdfCellOrder(const SdfCell& cell) {
  std::vector<SdfCellEntryRef> derived;
  derived.reserve(cell.iopaths.size() + cell.pulse_limits.size() +
                  cell.interconnects.size() + cell.devices.size() +
                  cell.specparams.size() + cell.timing_checks.size());
  for (uint32_t i = 0; i < cell.iopaths.size(); ++i) {
    derived.push_back({SdfCellEntryKind::kIopath, i});
  }
  for (uint32_t i = 0; i < cell.pulse_limits.size(); ++i) {
    derived.push_back({SdfCellEntryKind::kPulseLimit, i});
  }
  for (uint32_t i = 0; i < cell.interconnects.size(); ++i) {
    derived.push_back({SdfCellEntryKind::kInterconnect, i});
  }
  for (uint32_t i = 0; i < cell.devices.size(); ++i) {
    derived.push_back({SdfCellEntryKind::kDevice, i});
  }
  for (uint32_t i = 0; i < cell.specparams.size(); ++i) {
    derived.push_back({SdfCellEntryKind::kSpecparam, i});
  }
  for (uint32_t i = 0; i < cell.timing_checks.size(); ++i) {
    derived.push_back({SdfCellEntryKind::kTimingCheck, i});
  }
  return derived;
}

// §32.5: the SDF source one annotation is taken from -- the cell whose entry is
// being applied, the file it sits in, which an INTERCONNECT entry resolves its
// port names against, and the instance prefix the cell's CELLINSTANCE names.
//
// `inst_prefix` is what SdfCellPrefixInRegion (simulator/sdf_parser.h) made of
// the cell's instance path, read from the §32.9 region down: the
// hierarchical prefix of the module instance whose specify block declared the
// paths this cell annotates, in the spelling PathDelay::inst_prefix carries.
struct SdfCellSource {
  const SdfCell& cell;
  const SdfFile& file;
  std::string_view inst_prefix;
};

void AnnotateSdfCellEntry(const SdfCellSource& src,
                          const SdfCellEntryRef& entry, SpecifyManager& mgr,
                          SdfMtm mtm, SdfAnnotationResult& result) {
  const SdfCell& cell = src.cell;
  switch (entry.kind) {
    case SdfCellEntryKind::kIopath:
      AnnotateSdfIopathEntry(cell.iopaths[entry.index], src.inst_prefix, mgr,
                             mtm);
      break;
    case SdfCellEntryKind::kPulseLimit:
      AnnotateSdfPulseLimitEntry(cell.pulse_limits[entry.index],
                                 src.inst_prefix, mgr, mtm);
      break;
    case SdfCellEntryKind::kInterconnect:
      AnnotateSdfInterconnectEntry(cell.interconnects[entry.index], src.file,
                                   mgr, mtm, result);
      break;
    case SdfCellEntryKind::kDevice:
      AnnotateSdfDeviceEntry(cell.devices[entry.index], src.inst_prefix, mgr,
                             mtm, result);
      break;
    case SdfCellEntryKind::kSpecparam:
      AnnotateSdfSpecparamEntry(cell.specparams[entry.index], src.inst_prefix,
                                mgr, mtm);
      break;
    case SdfCellEntryKind::kTimingCheck:
      AnnotateSdfTimingCheckEntry(cell.timing_checks[entry.index],
                                  src.inst_prefix, mgr, mtm, result);
      break;
  }
}

// §32.5: annotation is an ordered process, so a cell's constructs are applied
// one after another in the order the file wrote them -- across the cell's
// sections, not merely within each one. That is what lets a construct's
// annotation be overwritten or modified by a later construct of a different
// kind: a LABEL that reprices a specparam a module path delay expression reads
// undoes an earlier IOPATH on that path, and an IOPATH written after the LABEL
// undoes the LABEL's effect on that path instead.
void AnnotateSdfCell(const SdfCellSource& src, SpecifyManager& mgr, SdfMtm mtm,
                     SdfAnnotationResult& result) {
  std::vector<SdfCellEntryRef> derived;
  const std::vector<SdfCellEntryRef>* order = &src.cell.entry_order;
  if (order->empty()) {
    derived = BuildDerivedSdfCellOrder(src.cell);
    order = &derived;
  }
  for (const auto& entry : *order) {
    AnnotateSdfCellEntry(src, entry, mgr, mtm, result);
  }
}

}  // namespace

SdfAnnotationResult AnnotateSdfToManager(const SdfFile& file,
                                         SpecifyManager& mgr, SdfMtm mtm,
                                         std::string_view region_prefix,
                                         std::string_view design_root) {
  SdfAnnotationResult result;

  // §32.3: every piece of SDF data the annotator could not take in gets its own
  // warning. The parser collects them as it goes; constructs that carry no
  // SystemVerilog timing at all (the TIMINGENV section being the stock example)
  // never reach this list, because those are to be dropped silently.
  for (const auto& kw : file.unannotatable) {
    result.warnings.push_back("SDF annotator: unable to annotate " + kw +
                              " construct");
  }

  // §32.3: annotation is driven purely by what the file supplies. Nothing here
  // walks the manager's existing values, so a timing value the file says
  // nothing about keeps whatever it held before backannotation.
  for (const auto& cell : file.cells) {
    // §32.9: the cell's instance path, read from the region down, says which
    // instance of the cell the entries below annotate, and a cell it leaves
    // outside the region is not annotated. Working it out once here keeps
    // every entry of the cell reading the one answer.
    std::optional<std::string> prefix =
        SdfCellPrefixInRegion(cell.instance, region_prefix, design_root);
    if (!prefix.has_value()) continue;
    AnnotateSdfCell({cell, file, *prefix}, mgr, mtm, result);
  }
  return result;
}

bool ParseSdfMtmKeyword(std::string_view text, SdfMtmKeyword& out) {
  if (text == "MAXIMUM") {
    out = SdfMtmKeyword::kMaximum;
    return true;
  }
  if (text == "MINIMUM") {
    out = SdfMtmKeyword::kMinimum;
    return true;
  }
  if (text == "TYPICAL") {
    out = SdfMtmKeyword::kTypical;
    return true;
  }
  if (text == "TOOL_CONTROL") {
    out = SdfMtmKeyword::kToolControl;
    return true;
  }
  return false;
}

}  // namespace delta
