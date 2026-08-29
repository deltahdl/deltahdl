// Which cells an $sdf_annotate call reaches and the order one cell's
// constructs are applied in. §32.9 has a module_instance operand name a level
// of the design hierarchy: CellInScope narrows a file's cells to that level and
// below, and SdfCellInstancePrefix works out the instance prefix the entries of
// a cell carry, which is what holds an SDF record to the one module instance it
// names. §32.5 has annotation proceed in order, so AnnotateSdfCell walks a
// cell's constructs as the file wrote them, across its sections rather than
// within each, and AnnotateSdfCellEntry hands each construct to the function
// for its kind.
//
// Those six functions annotate the constructs of §32.4 and §32.7 and stand in
// simulator/sdf_annotate_entry.cpp, together with the §32.8 Table 32-4 delay
// expansion each of them reads. They are declared below rather than in
// simulator/sdf_parser.h because AnnotateSdfCellEntry is their only caller.

#include <cstddef>
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

// §32.9: a module_instance operand names a level of the design hierarchy, and
// the annotator works from that level down. A SystemVerilog hierarchical name
// divides its levels with '.' while an SDF instance path divides them with '/',
// so the two are compared level by level with either divider accepted rather
// than as raw text.
bool CellInScope(std::string_view instance, std::string_view scope) {
  if (scope.empty()) return true;
  if (instance.size() < scope.size()) return false;
  for (std::size_t i = 0; i < scope.size(); ++i) {
    const char kInst = instance[i];
    const char kScope = scope[i];
    const bool kBothDividers =
        (kInst == '/' || kInst == '.') && (kScope == '/' || kScope == '.');
    if (kInst != kScope && !kBothDividers) return false;
  }
  if (instance.size() == scope.size()) return true;
  const char kSep = instance[scope.size()];
  return kSep == '/' || kSep == '.';
}

// §32.9: the cells the module_instance operand selects sit at or below the
// level it names, so what tells two of them apart is the part of the SDF
// instance path below that level. PathDelay::inst_prefix names the same thing
// on the SystemVerilog side, in the spelling Lowerer::inst_prefix_ produces,
// so the remainder is rewritten into that spelling here: '/' dividers become
// '.', and a trailing '.' closes it. The scope root itself has no remainder
// and answers empty, which is the prefix a module elaborated as a top carries.
std::string SdfCellInstancePrefix(std::string_view instance,
                                  std::string_view design_root) {
  if (design_root.empty()) return {};
  if (instance == design_root) return {};
  std::string_view rest = instance;
  // A file may write the cell's path from the root or from below it. Strip the
  // root's own segment where it is there, and take what is left as written
  // where it is not.
  if (rest.size() > design_root.size() &&
      rest.substr(0, design_root.size()) == design_root &&
      (rest[design_root.size()] == '/' || rest[design_root.size()] == '.')) {
    rest = rest.substr(design_root.size() + 1);
  }
  std::string prefix(rest);
  for (char& divider : prefix) {
    if (divider == '/') divider = '.';
  }
  if (!prefix.empty()) prefix.push_back('.');
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
// `inst_prefix` is what SdfCellInstancePrefix (simulator/sdf_parser.h) made of
// the cell's instance path against the §32.9 module_instance operand: the
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
                                         std::string_view scope,
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
    if (!CellInScope(cell.instance, scope)) continue;
    // §32.9: the operand selected the cell, and the part of its instance path
    // below the operand's level is what says which instance of the cell the
    // entries below annotate. Working it out once here keeps every entry of
    // the cell reading the one answer.
    std::string prefix = SdfCellInstancePrefix(cell.instance, design_root);
    AnnotateSdfCell({cell, file, prefix}, mgr, mtm, result);
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
