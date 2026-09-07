#include <string_view>
#include <utility>

#include "common/diagnostic.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_viewport.h"

namespace delta {

void Preprocessor::ApplyViewport(const PragmaKeywordExpression& expr,
                                 SourceLoc loc) {
  // §34.5.32.2 has a viewport describe objects within the current protected
  // envelope, so the ones an envelope was described by belong to that envelope
  // and to no other. §34.2 permits the nesting -- "Decryption envelopes may
  // contain other envelopes within their enclosed data block" -- so which
  // envelope is current changes as one opens and closes inside another, and
  // the outer envelope is current again when the inner one has closed, still
  // described by what it wrote.
  //
  // The viewports were held in one flat list cleared at every boundary, so an
  // inner envelope's opening wiped the outer's and nothing put them back. They
  // are a stack now, mirroring the envelope nesting that
  // ProtectEnvelopeState::Close already keeps: an open puts the current
  // envelope's aside and starts an empty list for the one opening, and a close
  // takes the enclosing one back.
  if (OpensEncryptionEnvelope(expr.keyword, expr.has_value) ||
      OpensDecryptionEnvelope(expr.keyword, expr.has_value)) {
    protect_viewport_stack_.push_back(std::move(protect_viewports_));
    protect_viewports_.clear();
    return;
  }
  if (ClosesEncryptionEnvelope(expr.keyword, expr.has_value) ||
      ClosesDecryptionEnvelope(expr.keyword, expr.has_value)) {
    // A close standing where nothing was opened has no enclosing envelope to
    // give back, and the list it ends is the one written outside every
    // envelope, which describes nothing.
    if (protect_viewport_stack_.empty()) {
      protect_viewports_.clear();
      return;
    }
    protect_viewports_ = std::move(protect_viewport_stack_.back());
    protect_viewport_stack_.pop_back();
    return;
  }
  if (expr.keyword != kViewportKeyword) return;
  ProtectViewport viewport =
      ParseProtectViewport(expr.value.empty() ? expr.value_list : expr.value);
  // §34.5.32.1 writes the value as an object and an access, each against a
  // string. A value written any other way describes no object, so there is
  // nothing for the access it asks to be permitted for.
  if (!viewport.stated) {
    diag_.Error(loc,
                "protect pragma viewport expression is written as an object "
                "and an access, each against a string",
                Subclause("34.5.32.1"));
    return;
  }
  // §34.5.32.2: the specified object name shall be contained within the
  // current envelope. Where no envelope is open there is no current envelope
  // for it to be contained within, whichever object the expression named.
  if (!protect_envelopes_.InProtectedRegion() &&
      protect_envelopes_.EncryptionEnvelopeDepth() == 0) {
    diag_.Error(loc,
                "protect pragma viewport expression stands in no protected "
                "envelope for its object to be contained within",
                Subclause("34.5.32.2"));
    return;
  }
  // §34.5.32.2 asks for an access it does not define: the access value is an
  // implementation-specific relaxation of protection, and what it relaxes is
  // the protection §37.3.6 gives an object sealed in a decryption envelope,
  // whose properties a VPI application may read none of. This tool seals no
  // such object. VpiObject::is_protected in src/simulator/vpi_object.h is what
  // carries that protection, and no path from a decryption envelope sets it,
  // so a reader of a region this preprocessor decrypted reaches every object
  // of it whether a viewport named that object or not. The expression is
  // reported for that reason: a text that named one object to be reachable is
  // entitled to hear that all of them are. #3284 carries what would replace
  // the report: the containment rule checked where names resolve, and access
  // values written down for a protection that exists to be relaxed.
  diag_.Warning(loc,
                "protect pragma viewport expression is not acted on: this "
                "tool withholds no access to a decryption envelope's objects, "
                "so it grants the access the viewport asks for and every "
                "other access besides",
                Subclause("34.5.32"));
  protect_viewports_.push_back(std::move(viewport));
}

}  // namespace delta
