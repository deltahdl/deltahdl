#pragma once

#include <optional>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/envelope_viewport.h"
#include "common/source_mgr.h"
#include "parser/ast_design.h"

namespace delta {

struct ViewportTarget {
  std::string_view definition;
  std::string path;
};

std::optional<ViewportTarget> ResolveViewport(const CompilationUnit& unit,
                                              const EnvelopeViewport& viewport,
                                              const SourceManager& sources);

void ReportViewportsContainingNothing(const CompilationUnit& unit,
                                      DiagEngine& diag);

}  // namespace delta
