#pragma once

#include "common/source_loc.h"
#include "parser/ast_type.h"

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

// A friend of Parser, which reads what opens a data_declaration for the module
// item and block item paths alike: its qualifiers, and a type named through
// `$unit ::` (src/parser/parser_block_item_decl.cpp); the signing after a type
// keyword (src/parser/parser_types.cpp); and a class property's data type
// (src/parser/parser_items_data_decl.cpp).
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

  // Whether `kind` is one A.2.2.1 counts an integer_atom_type (byte,
  // shortint, int, longint, integer, time) or an integer_vector_type (bit,
  // logic, reg).
  static bool IsIntegerAtomKind(DataTypeKind kind);
  static bool IsIntegerVectorKind(DataTypeKind kind);

  // Reads a signing standing after the type `dtype` holds so far. A.2.2.1
  // writes one after an integer vector or atom type, and A.2.1.3 after a net
  // type keyword no data type keyword follows, where it opens the net's
  // implicit_data_type; after any other type it is reported under A.2.2.1 and
  // passed over.
  static void ReadSigning(Parser& p, DataType& dtype);

  // Reads a class property's data type. A.1.9 makes the property a
  // data_declaration behind its qualifiers, which A.2.1.3 opens with an
  // optional `var`; footnote 14 of A.10 lets the type after `var` be implicit.
  static DataType ReadClassPropertyType(Parser& p);
};

}  // namespace delta
