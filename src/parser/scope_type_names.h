#pragma once

#include <string_view>
#include <unordered_map>
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

// Everything one file's parse leaves the files after it on the same command
// line, which §3.12.1 case a) makes one compilation unit with it: "all files on
// a given compilation command line make a single compilation unit (in which
// case the declarations within those files are accessible following normal
// visibility rules throughout the entire set of files)".
//
// `own` is what the compilation-unit scope itself declared, and it decides how
// a later file parses on its own: `byte_t b;` reads as an instantiation of a
// module called byte_t until byte_t is known to be a type. `packages` and
// `classes` are what those names can be put back by -- §26.3's import
// declaration "allows identifiers declared within packages to be visible within
// the current scope without a package name qualifier", and §8.13's extends
// clause gives a derived class the type names of its base -- so a file
// importing a package another file declared needs the package's entry to have
// crossed with it.
//
// The three travel together because a caller that carries one and not the
// others has a compilation unit that is partly shared, which is not a state
// §3.12.1 describes.
struct CompilationUnitScopeNames {
  ScopeTypeNames own;
  std::unordered_map<std::string_view, ScopeTypeNames> packages;
  std::unordered_map<std::string_view, ScopeTypeNames> classes;
};

// Adds everything `src` holds to `target`, for a caller accumulating the scope
// across a command line. A name already in `target` stays as it is: the file
// that declared it first is the one a later file's reference resolves to, which
// is the order §26.3 states -- "The compilation of a package shall precede the
// compilation of scopes in which the package is imported."
inline void MergeCompilationUnitScope(CompilationUnitScopeNames& target,
                                      const CompilationUnitScopeNames& src) {
  target.own.types.insert(src.own.types.begin(), src.own.types.end());
  target.own.nettypes.insert(src.own.nettypes.begin(), src.own.nettypes.end());
  target.packages.insert(src.packages.begin(), src.packages.end());
  target.classes.insert(src.classes.begin(), src.classes.end());
}

}  // namespace delta
