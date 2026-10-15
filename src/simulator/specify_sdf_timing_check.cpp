// §32.4.2: an SDF TIMINGCHECK annotation placed on the declared timing checks
// it matches, with §31.9.1's adjustment of a limit annotated onto a check
// evaluated on delayed signals.

#include <charconv>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_specify.h"
#include "simulator/specify.h"
#include "simulator/specify_internal.h"
#include "simulator/specify_sdf.h"
#include "simulator/specify_timing_check.h"

namespace delta {

namespace {

// §32.4.2: whether the select an SDF signal was written with, `[0]` or
// `[3:2]`, names the select `declared` the check's terminal was written with.
// A signal written with none names the terminal whatever select it carries.
bool SdfSelectNames(const std::string& written,
                    const TerminalSelect& declared) {
  if (written.empty()) return true;
  if (!declared.present || written.size() < 3) return false;
  const std::string_view kInner(written.data() + 1, written.size() - 2);
  const std::size_t kColon = kInner.find(':');
  const std::string_view kLeft = kInner.substr(0, kColon);
  const std::string_view kRight =
      kColon == std::string_view::npos ? kLeft : kInner.substr(kColon + 1);
  int64_t left = 0;
  int64_t right = 0;
  std::from_chars(kLeft.data(), kLeft.data() + kLeft.size(), left);
  std::from_chars(kRight.data(), kRight.data() + kRight.size(), right);
  return declared.left == left && declared.right == right;
}

// §32.4.2: whether the edge an SDF signal was written with names the edge the
// check's event on that signal was written with. A signal written with none
// matches any edge; a transition, 01 or 1z, matches the declaration written
// with that one descriptor.
bool SdfEdgeNames(
    SpecifyEdge written,
    const std::vector<std::pair<char, char>>& written_descriptors,
    SpecifyEdge declared,
    const std::vector<std::pair<char, char>>& declared_descriptors) {
  if (written == SpecifyEdge::kNone) return true;
  if (declared != written) return false;
  return written != SpecifyEdge::kEdge ||
         declared_descriptors == written_descriptors;
}

// Whether the condition an SDF signal was written with names `declared`, the
// condition the check's event on that signal was written with. A signal the
// file wrote with none matches whatever condition it carries.
bool SdfConditionNames(const std::string& written, const Expr* declared) {
  return written.empty() ||
         SpecifyConditionsMatch(SpecifyConditionText(declared), written);
}

bool SdfAnnotationMatchesCheck(const TimingCheckEntry& existing,
                               const SdfTcAnnotation& a,
                               std::string_view inst_prefix) {
  // §31.2 puts a system timing check inside a specify block, so two instances
  // of one cell declare checks naming identically spelled signals and the
  // instance is what tells them apart. The prefixes are compared exactly, an
  // empty one naming the module the design was elaborated as rather than every
  // instance: SdfCellPrefixInRegion (simulator/sdf_parser.h) answers a definite
  // prefix for every cell, so no annotation arrives with its instance left
  // unspecified. The SpecifyEdge::kNone and the empty condition below do reach
  // a check carrying any edge or any condition, which is what §32.4.2 rules for
  // an SDF check whose signals the file wrote no edge and no condition on.
  if (existing.inst_prefix != inst_prefix) return false;
  if (existing.kind != a.kind) return false;
  if (existing.ref_signal != a.ref_signal) return false;
  if (existing.data_signal != a.data_signal) return false;
  if (!SdfSelectNames(a.ref_select, existing.ref_select)) return false;
  if (!SdfSelectNames(a.data_select, existing.data_select)) return false;
  if (!SdfEdgeNames(a.ref_edge, a.ref_edge_descriptors, existing.ref_edge,
                    existing.ref_edge_descriptors) ||
      !SdfEdgeNames(a.data_edge, a.data_edge_descriptors, existing.data_edge,
                    existing.data_edge_descriptors)) {
    return false;
  }
  // §32.4.2: a condition the file wrote on a signal has to match the one the
  // declaration wrote on that same signal.
  return SdfConditionNames(a.ref_condition, existing.ref_condition_expr) &&
         SdfConditionNames(a.data_condition, existing.data_condition_expr);
}

// §31.9.1: an annotated limit of a check evaluated on delayed signals is
// adjusted for their delays as a declared one was, and set to 0 with a warning
// where that leaves it no longer positive.
uint64_t AnnotatedLimit(uint64_t limit, int64_t shift,
                        std::vector<std::string>& warnings) {
  const AdjustedNegativeTimingLimit kAdjusted =
      ShiftTimingCheckLimit(limit, shift);
  if (kAdjusted.warn) {
    warnings.emplace_back(
        "SDF annotator: adjusted for the delays of the delayed signals its "
        "check is evaluated on, an annotated limit is no longer positive and "
        "is set to 0");
  }
  return kAdjusted.limit;
}

// §32.4.2: the annotation replaces the signed limits a negative check reads.
// One annotated limit and its signed form. A value annotated below zero keeps
// its sign in the signed form, which §31.9 reads on a $setuphold or a $recrem
// under the enabling option, and reads as 0 in the unsigned one every other
// reader takes.
void ApplySdfLimit(uint64_t& limit, int64_t& signed_limit, int64_t value,
                   int64_t shift, std::vector<std::string>& warnings) {
  limit = AnnotatedLimit(value < 0 ? 0 : static_cast<uint64_t>(value), shift,
                         warnings);
  signed_limit = value < 0 ? value : static_cast<int64_t>(limit);
}

void ApplySdfAnnotationFields(TimingCheckEntry& check, const SdfTcAnnotation& a,
                              const TimingCheckInvocationOptions& options,
                              std::vector<std::string>& warnings) {
  const int64_t kFirstShift = FirstLimitDelayShift(check);
  if (a.set_limit) {
    ApplySdfLimit(check.limit, check.signed_limit, a.limit, kFirstShift,
                  warnings);
  }
  if (a.set_limit2) {
    ApplySdfLimit(check.limit2, check.signed_limit2, a.limit2, -kFirstShift,
                  warnings);
  }
  // §31.9.4: a negative value annotated onto a $setuphold or a $recrem is
  // honored as one declared there would be, under the enabling option.
  const bool kTakesNegative = check.kind == TimingCheckKind::kSetuphold ||
                              check.kind == TimingCheckKind::kRecrem;
  if (kTakesNegative && (check.signed_limit < 0 || check.signed_limit2 < 0)) {
    check.negative_timing_check_enabled =
        NegativeTimingCheckValuesAccepted(true, options);
  }
  if (a.set_start_edge_offset) {
    check.start_edge_offset = a.start_edge_offset + check.delayed_signal_shift;
  }
  if (a.set_end_edge_offset) {
    check.end_edge_offset = a.end_edge_offset - check.delayed_signal_shift;
  }
}

}  // namespace

bool SpecifyManager::AnnotateSdfTimingCheck(
    const SdfTcAnnotation& a, std::string_view inst_prefix,
    std::vector<std::string>& warnings) {
  // §32.1: SDF back-annotates the timing checks a design already declares in
  // its specify blocks; it never introduces a new check. A single SDF check
  // (e.g. SETUPHOLD) expands into several candidate annotations (setup, hold,
  // setuphold) so it can update whichever representation the specify block
  // uses; candidates that match nothing are simply dropped, not appended.
  // Appending them would fabricate checks the RTL never declared (turning one
  // SETUPHOLD into three entries).
  bool applied = false;
  for (auto& existing : timing_checks_) {
    if (!SdfAnnotationMatchesCheck(existing, a, inst_prefix)) continue;
    ApplySdfAnnotationFields(existing, a, timing_check_options_, warnings);
    applied = true;
  }
  return applied;
}

}  // namespace delta
