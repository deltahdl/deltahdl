#include <charconv>
#include <cstddef>
#include <cstdint>
#include <optional>
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

bool SdfConditionNames(const std::string& written, const Expr* declared) {
  return written.empty() ||
         SpecifyConditionsMatch(SpecifyConditionText(declared), written);
}

bool SdfAnnotationMatchesCheck(const TimingCheckEntry& existing,
                               const SdfTcAnnotation& a,
                               std::string_view inst_prefix) {
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
  return SdfConditionNames(a.ref_condition, existing.ref_condition_expr) &&
         SdfConditionNames(a.data_condition, existing.data_condition_expr);
}

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

void ApplySdfLimit(uint64_t& limit, int64_t& signed_limit, int64_t value,
                   int64_t shift, std::vector<std::string>& warnings) {
  limit = AnnotatedLimit(value < 0 ? 0 : static_cast<uint64_t>(value), shift,
                         warnings);
  signed_limit = value < 0 ? value : static_cast<int64_t>(limit);
}

void SettleNegativeHandling(TimingCheckEntry& check, const SdfTcAnnotation& a,
                            const TimingCheckInvocationOptions& options,
                            int64_t delayed_shift) {
  const bool kTakesNegative = check.kind == TimingCheckKind::kSetuphold ||
                              check.kind == TimingCheckKind::kRecrem;
  if (kTakesNegative && (a.set_limit || a.set_limit2)) {
    const int64_t kFirst = a.set_limit ? a.limit : check.signed_limit;
    const int64_t kSecond = a.set_limit2 ? a.limit2 : check.signed_limit2;
    check.negative_timing_check_enabled =
        NegativeTimingCheckValuesAccepted(kFirst < 0 || kSecond < 0, options);
  }
  check.delayed_signal_shift =
      EvaluatedOnDelayedSignals(check) ? delayed_shift : 0;
}

struct SdfLimitPlace {
  uint64_t& limit;
  int64_t& signed_limit;
};

void PlaceSdfLimit(SdfLimitPlace place, std::optional<int64_t> annotated,
                   int64_t shift, int64_t moved,
                   std::vector<std::string>& warnings) {
  if (annotated.has_value()) {
    ApplySdfLimit(place.limit, place.signed_limit, *annotated, shift, warnings);
    return;
  }
  if (moved != 0) {
    ApplySdfLimit(place.limit, place.signed_limit, place.signed_limit, moved,
                  warnings);
  }
}

void ApplySdfAnnotationFields(TimingCheckEntry& check, const SdfTcAnnotation& a,
                              const TimingCheckInvocationOptions& options,
                              int64_t delayed_shift,
                              std::vector<std::string>& warnings) {
  const int64_t kPriorShift = FirstLimitDelayShift(check);
  SettleNegativeHandling(check, a, options, delayed_shift);
  const int64_t kFirstShift = FirstLimitDelayShift(check);
  const int64_t kMoved = kFirstShift - kPriorShift;
  PlaceSdfLimit({check.limit, check.signed_limit},
                a.set_limit ? std::optional<int64_t>(a.limit) : std::nullopt,
                kFirstShift, kMoved, warnings);
  PlaceSdfLimit({check.limit2, check.signed_limit2},
                a.set_limit2 ? std::optional<int64_t>(a.limit2) : std::nullopt,
                -kFirstShift, -kMoved, warnings);
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
  bool applied = false;
  for (auto& existing : timing_checks_) {
    if (!SdfAnnotationMatchesCheck(existing, a, inst_prefix)) continue;
    ApplySdfAnnotationFields(existing, a, timing_check_options_,
                             DelayedSignalShift(existing), warnings);
    applied = true;
  }
  return applied;
}

}  // namespace delta
