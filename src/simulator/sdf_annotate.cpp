#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/sdf_annotate_internal.h"
#include "simulator/sdf_parser.h"

namespace delta {

void AnnotateSdfIopathEntry(const SdfIopath& io, std::string_view inst_prefix,
                            SpecifyManager& mgr, SdfMtm mtm,
                            SdfAnnotationResult& result);
void AnnotateSdfPulseLimitEntry(const SdfPulseLimit& pl,
                                std::string_view inst_prefix,
                                SpecifyManager& mgr, SdfMtm mtm,
                                SdfAnnotationResult& result);
void AnnotateSdfInterconnectEntry(const SdfInterconnect& ic,
                                  const SdfCellSource& src, SpecifyManager& mgr,
                                  SdfMtm mtm, SdfAnnotationResult& result);
void AnnotateSdfDeviceEntry(const SdfDevice& dev, std::string_view inst_prefix,
                            SpecifyManager& mgr, SdfMtm mtm,
                            SdfAnnotationResult& result);
void AnnotateSdfSpecparamEntry(const SdfSpecparam& sp,
                               std::string_view inst_prefix,
                               SpecifyManager& mgr, SdfMtm mtm,
                               SdfAnnotationResult& result);
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

void AnnotateSdfCellEntry(const SdfCellSource& src,
                          const SdfCellEntryRef& entry, SpecifyManager& mgr,
                          SdfMtm mtm, SdfAnnotationResult& result) {
  const SdfCell& cell = src.cell;
  switch (entry.kind) {
    case SdfCellEntryKind::kIopath:
      AnnotateSdfIopathEntry(cell.iopaths[entry.index], src.inst_prefix, mgr,
                             mtm, result);
      break;
    case SdfCellEntryKind::kPulseLimit:
      AnnotateSdfPulseLimitEntry(cell.pulse_limits[entry.index],
                                 src.inst_prefix, mgr, mtm, result);
      break;
    case SdfCellEntryKind::kInterconnect:
      AnnotateSdfInterconnectEntry(cell.interconnects[entry.index], src, mgr,
                                   mtm, result);
      break;
    case SdfCellEntryKind::kDevice:
      AnnotateSdfDeviceEntry(cell.devices[entry.index], src.inst_prefix, mgr,
                             mtm, result);
      break;
    case SdfCellEntryKind::kSpecparam:
      AnnotateSdfSpecparamEntry(cell.specparams[entry.index], src.inst_prefix,
                                mgr, mtm, result);
      break;
    case SdfCellEntryKind::kTimingCheck:
      AnnotateSdfTimingCheckEntry(cell.timing_checks[entry.index],
                                  src.inst_prefix, mgr, mtm, result);
      break;
  }
}

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

  for (const auto& kw : file.unannotatable) {
    result.warnings.push_back("SDF annotator: unable to annotate " + kw +
                              " construct");
  }

  for (const auto& cell : file.cells) {
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
