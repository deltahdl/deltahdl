#include <string>
#include <string_view>
#include <utility>

#include "common/diagnostic.h"
#include "common/envelope_viewport.h"
#include "common/source_loc.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_viewport.h"

namespace delta {

void Preprocessor::ApplyViewport(const PragmaKeywordExpression& expr,
                                 SourceLoc loc) {
  if (OpensEncryptionEnvelope(expr.keyword, expr.has_value) ||
      OpensDecryptionEnvelope(expr.keyword, expr.has_value)) {
    protect_viewport_stack_.push_back(
        {std::move(protect_viewports_), protect_envelope_source_,
         protect_envelope_opened_at_, protect_envelope_first_source_});
    protect_viewports_.clear();
    protect_envelope_source_ = 0;
    protect_envelope_opened_at_ = loc;
    protect_envelope_first_source_ = src_mgr_.LastFileId() + 1;
    return;
  }
  if (ClosesDecryptionEnvelope(expr.keyword, expr.has_value)) {
    RecordEnvelopeViewports();
  }
  if (ClosesEncryptionEnvelope(expr.keyword, expr.has_value)) {
    RecordRegionViewports(loc);
  }
  if (ClosesEncryptionEnvelope(expr.keyword, expr.has_value) ||
      ClosesDecryptionEnvelope(expr.keyword, expr.has_value)) {
    if (protect_viewport_stack_.empty()) {
      protect_viewports_.clear();
      protect_envelope_source_ = 0;
      return;
    }
    EnclosingViewports& enclosing = protect_viewport_stack_.back();
    protect_viewports_ = std::move(enclosing.viewports);
    protect_envelope_source_ = enclosing.envelope_source;
    protect_envelope_opened_at_ = enclosing.opened_at;
    protect_envelope_first_source_ = enclosing.first_source;
    protect_viewport_stack_.pop_back();
    return;
  }
  if (expr.keyword != kViewportKeyword) return;
  ProtectViewport viewport =
      ParseProtectViewport(expr.value.empty() ? expr.value_list : expr.value);
  if (!viewport.stated) {
    diag_.Error(loc,
                "protect pragma viewport expression is written as an object "
                "and an access, each against a string",
                Subclause("34.5.32.1"));
    return;
  }
  if (!protect_envelopes_.InProtectedRegion() &&
      protect_envelopes_.EncryptionEnvelopeDepth() == 0) {
    diag_.Error(loc,
                "protect pragma viewport expression stands in no protected "
                "envelope for its object to be contained within",
                Subclause("34.5.32.2"));
    return;
  }
  if (ViewportAccessOf(viewport.access) == ViewportAccess::kNone) {
    diag_.Warning(loc,
                  "protect pragma viewport access \"" + viewport.access +
                      "\" is not one this tool defines (\"r\" or \"rw\"), "
                      "so the object the viewport names stays protected",
                  Subclause("34.5.32.2"));
  }
  viewport.loc = loc;
  protect_viewports_.push_back(std::move(viewport));
}

namespace {

EnvelopeViewport KeptViewport(const ProtectViewport& viewport) {
  EnvelopeViewport kept;
  kept.object = viewport.object;
  kept.access = viewport.access;
  kept.loc = viewport.loc;
  return kept;
}

}  // namespace

void Preprocessor::RecordEnvelopeViewports() {
  if (protect_envelope_source_ == 0) return;
  for (const ProtectViewport& viewport : protect_viewports_) {
    EnvelopeViewport kept = KeptViewport(viewport);
    kept.first_source = protect_envelope_source_;
    kept.last_source = src_mgr_.LastFileId();
    src_mgr_.AddViewport(std::move(kept));
  }
}

void Preprocessor::RecordRegionViewports(SourceLoc closed_at) {
  if (closed_at.file_id != protect_envelope_opened_at_.file_id) return;
  for (const ProtectViewport& viewport : protect_viewports_) {
    EnvelopeViewport kept = KeptViewport(viewport);
    kept.first_source = protect_envelope_first_source_;
    kept.last_source = src_mgr_.LastFileId();
    kept.region_source = closed_at.file_id;
    kept.first_line = protect_envelope_opened_at_.line;
    kept.last_line = closed_at.line;
    src_mgr_.AddViewport(std::move(kept));
  }
}

}  // namespace delta
