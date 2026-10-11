#pragma once

#include <string_view>

#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

// §10.9.1 and §10.9.2 (printed pages 262 and 264): an assignment pattern's
// type key names a type, written as a built-in type keyword or as the name of
// a typedef in scope (Syntax 10-5's simple_type), and applies to each element
// or member whose type matches it as §6.22.1 defines matching types.
bool IsTypeKey(std::string_view key, const TypedefMap& typedefs);

// Whether the type key `key` matches `type`: both resolved through their
// typedefs, an enum, structure or union by the declaration it came from, and
// any other type by its kind and its packed width, so `logic` does not match
// `logic [7:0]` and a typedef of int matches `int`.
bool TypeKeyMatchesType(std::string_view key, const DataType& type,
                        const TypedefMap& typedefs);

// The same for a structure member, an unpacked array member matching no key.
bool TypeKeyMatchesMember(std::string_view key, const StructMember& member,
                          const TypedefMap& typedefs);

}  // namespace delta
