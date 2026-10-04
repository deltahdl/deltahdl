#pragma once

#include <optional>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/envelope_viewport.h"
#include "common/source_mgr.h"
#include "parser/ast_design.h"

namespace delta {

// The declaration a viewport's object name resolves to: the design element
// whose instances hold it, and its path within each of them.
struct ViewportTarget {
  std::string_view definition;
  std::string path;
};

// §34.5.32.2: the declaration within its envelope that `viewport` names, or
// none.
//
// The subclause requires the object to be contained within the envelope, and
// §34.4 makes the envelope a lexical region, so the name is resolved against
// the declarations of the envelope's own text, from the scope the envelope
// stands in. A name that begins with a design element the envelope declares,
// `secret.q`, names an item of that element, and so of every instance of it.
// Where the envelope stands inside a design element instead, a name such as
// `q` names an item the envelope declares there. A later component reaches
// into an instance of a design element the envelope also declares, or into a
// generate block, as a hierarchical name does (§23.6).
std::optional<ViewportTarget> ResolveViewport(const CompilationUnit& unit,
                                              const EnvelopeViewport& viewport,
                                              const SourceManager& sources);

// §34.5.32.2: each viewport the reading recorded whose object name resolves
// to no declaration contained within its envelope is an error, reported where
// the viewport was written.
void ReportViewportsContainingNothing(const CompilationUnit& unit,
                                      DiagEngine& diag);

}  // namespace delta
