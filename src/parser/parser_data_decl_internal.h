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
// reads a data_declaration's qualifiers for the module item and block item
// paths alike.
struct ParserDataDeclHelpers {
  // Reads every `const`, `var`, `static` and `automatic` from the current
  // token on, in whatever order the source wrote them, so that the
  // declaration still parses. Each written after a qualifier A.2.1.3 places
  // after it, or written a second time, is reported under A.2.1.3.
  static DataDeclQualifiers ReadQualifiers(Parser& p);
};

}  // namespace delta
