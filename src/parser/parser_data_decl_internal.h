#pragma once

#include <optional>

#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_type.h"

namespace delta {

class Parser;

struct DataDeclQualifiers {
  bool is_const = false;
  bool has_var = false;
  bool is_automatic = false;
  bool is_static = false;
  SourceLoc lifetime_loc;
};

bool IsNetTypeToken(TokenKind tk);

std::optional<DataTypeKind> TokenToTypeKind(TokenKind tk);

struct ParserDataDeclHelpers {
  static DataDeclQualifiers ReadQualifiers(Parser& p);

  static bool AtUnitScopedTypeName(Parser& p);

  static bool IsIntegerAtomKind(DataTypeKind kind);
  static bool IsIntegerVectorKind(DataTypeKind kind);

  static void ReadSigning(Parser& p, DataType& dtype);

  static DataType ReadClassPropertyType(Parser& p);

  static DataType ReadDeclaredTypeOfAName(Parser& p);

  static bool ReadTypeReference(Parser& p, DataType& dtype);

  static bool AtTypeReference(Parser& p);

  static bool ReadKeyedTypeReference(Parser& p, DataType& dtype, bool has_var,
                                     bool is_port);

  static bool AtIndexType(Parser& p);

  static DataType ReadIndexDataType(Parser& p);
};

}  // namespace delta
