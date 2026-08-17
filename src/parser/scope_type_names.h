#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>

namespace delta {

// The type names, the nettype names and the user-defined primitive names one
// scope declared, as one value.
// §6.6.7's nettype declaration registers a name as a type name and as a nettype
// name both, so anything that carries a scope's type names to another scope has
// to carry both or lose the nettype half.
//
// The primitive names travel with them because a primitive name decides how a
// later item parses, exactly as a type name does.
// Parser::ParseImplicitTypeOrInst at src/parser/parser_items.cpp:795 reads an
// item's leading name as a primitive instantiation only when the parse has
// already seen that name declared by a udp_declaration, and §3.12.1 case a)
// makes a primitive declared in one file of a command line visible in the files
// after it. A parse that has not been told the name is a primitive reads
// `myudp #5 u (q, d);` as a module instantiation whose `#5` is a parameter
// value assignment, so the gate delay §29.8 writes there is dropped with
// nothing reported.
//
// A package's entry and a class's entry leave `udps` empty, because A.1.2
// admits udp_declaration only as a description at the outermost level: neither
// A.1.11's package_item and package_or_generate_item_declaration nor A.1.9's
// class_item lists it. Parser::TypeNameScope::NamesAddedSoFar in
// src/parser/parser.h is what fills those entries, and it answers with the type
// names and the nettype names alone.
//
// A name is held as a view into the source text the lexer read it out of, which
// SourceManager owns for as long as the run lasts. Carrying one from the parse
// of one file to the parse of another is therefore sound, and §3.12.1 case a)
// is what asks for it: the files of one command line share a compilation-unit
// scope, so a type name one of them declared there is a type name in the next.
struct ScopeTypeNames {
  std::unordered_set<std::string_view> types;
  std::unordered_set<std::string_view> nettypes;
  std::unordered_set<std::string_view> udps;
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
  target.own.udps.insert(src.own.udps.begin(), src.own.udps.end());
  target.packages.insert(src.packages.begin(), src.packages.end());
  target.classes.insert(src.classes.begin(), src.classes.end());
}

}  // namespace delta
