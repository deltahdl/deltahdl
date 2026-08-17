#pragma once

#include <string_view>
#include <unordered_set>

namespace delta {

// The type names and the nettype names one scope declared, as one value.
// §6.6.7's nettype declaration registers a name as a type name and as a nettype
// name both, so anything that carries a scope's type names to another scope has
// to carry both or lose the nettype half.
//
// A name is held as a view into the source text the lexer read it out of, which
// SourceManager owns for as long as the run lasts. Carrying one from the parse
// of one file to the parse of another is therefore sound, and §3.12.1 case a)
// is what asks for it: the files of one command line share a compilation-unit
// scope, so a type name one of them declared there is a type name in the next.
struct ScopeTypeNames {
  std::unordered_set<std::string_view> types;
  std::unordered_set<std::string_view> nettypes;
};

}  // namespace delta
