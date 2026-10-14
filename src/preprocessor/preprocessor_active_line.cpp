// §22.2: the routing of one comment-stripped active line between the text it
// holds and the directive it opens, and §22.4's rule on what may share a line
// with an `include.

#include <string>
#include <string_view>

#include "preprocessor/preprocessor_internal.h"

namespace delta {

void EmitActiveLine(std::string_view view, const ActiveLineEmit& emit,
                    std::string& output) {
  ActiveLineSplit split = ClassifyActiveLine(view);
  switch (split.kind) {
    case ActiveLineSplit::Kind::kLeadingDirective:
      if (split.split_pos > 0) output.append(view.substr(0, split.split_pos));
      emit.emit_directive_or_text(view.substr(split.split_pos));
      return;
    case ActiveLineSplit::Kind::kMidLineDirective:
      emit.expand_and_emit(view.substr(0, split.split_pos));
      // §22.4 (printed page 705): only white space or a comment may share an
      // `include's line, so one after a language element is reported.
      if (StartsWithDirective(view.substr(split.split_pos), "include"))
        emit.report_text_before_include();
      emit.emit_directive_or_text(view.substr(split.split_pos));
      return;
    default:  // ActiveLineSplit::Kind::kPlainText, the one kind left
      emit.expand_and_emit(view);
      return;
  }
}

}  // namespace delta
