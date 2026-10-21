#pragma once

#include "common/source_loc.h"

namespace delta {

class Parser;

// The qualifiers A.2.1.3 opens a data_declaration with, `[ const ] [ var ]
// [ lifetime ]`, as one declaration wrote them.
struct DataDeclQualifiers {
  bool is_const = false;
  bool has_var = false;
  bool is_automatic = false;
  bool is_static = false;
  // Where the lifetime keyword stands, when one was written.
  SourceLoc lifetime_loc;
};

// A friend of Parser, defined in src/parser/parser_block_item_decl.cpp, which
// reads what opens a data_declaration for the module item and block item paths
// alike: its qualifiers, and a type named through `$unit ::`.
struct ParserDataDeclHelpers {
  // Reads every `const`, `var`, `static` and `automatic` from the current
  // token on, in whatever order the source wrote them, so that the
  // declaration still parses. Each written after a qualifier A.2.1.3 places
  // after it, or written a second time, is reported under A.2.1.3.
  static DataDeclQualifiers ReadQualifiers(Parser& p);

  // Whether `$unit :: name` stands at the current token with `name` a type or
  // class the parser knows. A.9.3 makes `$unit ::` a package_scope, which
  // A.2.2.1 lets open a data_type (§3.12.1), but `$unit` is a system
  // identifier and the name after it may as well be a compilation-unit
  // variable, parameter or function that an expression reads, so it opens a
  // type on the terms a bare name does: when the name is a known type.
  static bool AtUnitScopedTypeName(Parser& p);
};

}  // namespace delta
