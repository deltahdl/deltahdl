#pragma once

#include <optional>

#include "common/source_loc.h"
#include "lexer/token.h"
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

// A.2.1.3: whether `tk` is one of the twelve net type keywords, `wire` to
// `uwire`. Defined in src/parser/parser_types.cpp.
bool IsNetTypeToken(TokenKind tk);

// The data type kind a type keyword opens, the net types' and `void`'s among
// them; empty for a token that is no type keyword. Defined in
// src/parser/parser_types.cpp.
std::optional<DataTypeKind> TokenToTypeKind(TokenKind tk);

// A friend of Parser, which reads what opens a data_declaration for the module
// item and block item paths alike: its qualifiers, and a type named through
// `$unit ::` (src/parser/parser_block_item_decl.cpp); the signing after a type
// keyword and a type reference (src/parser/parser_types.cpp); and a class
// property's data type (src/parser/parser_items_data_decl.cpp).
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
  // optional `var`; footnote 14 of A.10 lets the type after `var` be implicit,
  // and an implicit type without it is reported under §6.8.
  static DataType ReadClassPropertyType(Parser& p);

  // §6.23 with A.2.2.1: reads a type_reference, `type ( expression )`, into
  // `dtype` where the `type` keyword stands at the current token, and answers
  // whether it did. The argument is read as an expression whether it names a
  // value or a data type, and the elaborator tells the two apart
  // (Elaborator::ResolveTypeRef).
  static bool ReadTypeReference(Parser& p, DataType& dtype);

  // Whether a type_reference opens at the current token, `type` followed by
  // `(`. A.2.1.1 writes `type` followed by a name to open a type parameter's
  // declaration, and a value parameter's data type may be a type reference.
  static bool AtTypeReference(Parser& p);

  // ReadTypeReference for the data type of a declaration that may write `var`
  // before it, `has_var` saying whether it did. §6.23 has a type reference in
  // a variable's declaration follow `var` and in a net's follow a net type
  // keyword, which is read with the type it opens
  // (Parser::TryParseNetDataType), so one standing first without `var` is
  // reported. `is_port` names a port's declaration in the report, a port being
  // a net or a variable (§23.2.2.3).
  static bool ReadKeyedTypeReference(Parser& p, DataType& dtype, bool has_var,
                                     bool is_port);

  // A.2.5: whether an associative array's index, a data_type, opens at the
  // current token: a type keyword other than `void`, or a type an expression
  // cannot spell, an enumeration, structure or union declared there or a
  // parameterized class, `P#(8)`. A name alone, which may as well be a
  // constant sizing the array, is left to the expression reader. Defined in
  // src/parser/parser_assoc_index.cpp.
  static bool AtIndexType(Parser& p);
};

}  // namespace delta
