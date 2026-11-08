#include <cstddef>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "parser/parser.h"
#include "parser/parser_data_decl_internal.h"

namespace delta {

void Parser::ParseDataDeclItem(std::vector<ModuleItem*>& items, size_t before,
                               const std::vector<Attribute>& attrs) {
  const SourceLoc kRandLoc = CurrentLoc();
  bool is_rand = Match(TokenKind::kKwRand);
  if (is_rand && !InCheckerBody()) {
    diag_.Error(kRandLoc, "only a checker's data declaration opens with rand",
                Subclause("A.1.8"));
  }
  const DataDeclQualifiers kQuals =
      ParserDataDeclHelpers::ReadQualifiers(*this);
  if (kQuals.is_automatic) {
    diag_.Error(kQuals.lifetime_loc,
                "'automatic' is not allowed in a data_declaration outside "
                "a procedural context",
                Subclause("6.8"));
  }

  ParseTypedItemOrInst(items, kQuals);
  for (size_t i = before; i < items.size(); ++i) {
    if (is_rand) items[i]->is_rand = true;
    if (kQuals.is_automatic) items[i]->is_automatic = true;
    if (kQuals.is_static) items[i]->is_static = true;
  }
  AttachAttrs(items, before, attrs);
}

void Parser::ParseVarPrefixed(std::vector<ModuleItem*>& items, bool is_const) {
  const size_t kFirst = items.size();
  if (!TryParseTypeRef(items)) {
    DataType dtype;
    if (Check(TokenKind::kKwEnum)) {
      dtype = ParseEnumType();
    } else if (Check(TokenKind::kKwStruct) || Check(TokenKind::kKwUnion)) {
      dtype = ParseStructOrUnionType();
      ParsePackedDims(dtype);
    } else {
      dtype = ParseDeclaredDataType();
      if (dtype.kind == DataTypeKind::kImplicit &&
          Check(TokenKind::kLBracket)) {
        ParsePackedDims(dtype);
      }
    }
    if (is_const) dtype.is_const = true;
    ParseVarDeclList(items, dtype);
  }
  for (size_t i = kFirst; i < items.size(); ++i) {
    items[i]->has_explicit_var = true;
  }
}

static void ReportImplicitTypeWithoutVar(const DataType& dtype, SourceLoc loc,
                                         DiagEngine& diag) {
  if (dtype.kind != DataTypeKind::kImplicit) return;
  diag.Error(loc,
             "data_declaration without an explicit data type requires the "
             "'var' keyword",
             Subclause("6.8"));
}

static void ReportQualifiersBeforeItem(const DataDeclQualifiers& quals,
                                       SourceLoc loc, const char* msg,
                                       Subclause subclause, DiagEngine& diag) {
  if (!quals.is_const && !quals.is_static) return;
  diag.Error(loc, msg, subclause);
}

DataType ParserDataDeclHelpers::ReadClassPropertyType(Parser& p) {
  bool has_var = p.Match(TokenKind::kKwVar);
  SourceLoc type_loc = p.CurrentLoc();
  DataType dtype;
  if (p.Check(TokenKind::kKwType)) {
    if (!has_var) {
      p.diag_.Error(type_loc,
                    "type_reference in a variable declaration must be "
                    "preceded by the 'var' keyword",
                    Subclause("6.8"));
    }
    ReadTypeReference(p, dtype);
    return dtype;
  }
  if (!p.TryParseInlineAggregateType(dtype)) dtype = p.ParseDeclaredDataType();
  if (dtype.kind != DataTypeKind::kImplicit) return dtype;
  if (p.Check(TokenKind::kLBracket)) p.ParsePackedDims(dtype);
  if (has_var) return dtype;
  auto saved = p.lexer_.SavePos();
  p.Consume();
  bool unknown_type_name = p.CheckIdentifier();
  p.lexer_.RestorePos(saved);
  if (!unknown_type_name) {
    ReportImplicitTypeWithoutVar(dtype, type_loc, p.diag_);
  }
  return dtype;
}

void Parser::ParseTypedItemOrInst(std::vector<ModuleItem*>& items,
                                  const DataDeclQualifiers& quals) {
  if (quals.has_var) {
    ParseVarPrefixed(items, quals.is_const);
    return;
  }

  if (Check(TokenKind::kKwType)) {
    diag_.Error(CurrentLoc(),
                "type_reference in a variable declaration must be preceded "
                "by the 'var' keyword",
                Subclause("6.8"));
    TryParseTypeRef(items);
    return;
  }
  if (Check(TokenKind::kKwCase)) {
    ReportQualifiersBeforeItem(
        quals, CurrentLoc(),
        "a generate construct takes no const or lifetime qualifier",
        Subclause("A.4.2"), diag_);
    items.push_back(ParseGenerateCase());
    return;
  }
  if (IsAtGateKeyword()) {
    ReportQualifiersBeforeItem(
        quals, CurrentLoc(),
        "a gate instantiation takes no const or lifetime qualifier",
        Subclause("A.3.1"), diag_);
    RejectMisplacedGate();
    ParseGateInst(items);
    return;
  }
  if (Check(TokenKind::kKwEnum) || Check(TokenKind::kKwStruct) ||
      Check(TokenKind::kKwUnion)) {
    auto dtype =
        Check(TokenKind::kKwEnum) ? ParseEnumType() : ParseStructOrUnionType();
    ParsePackedDims(dtype);
    dtype.is_const = quals.is_const;
    ParseVarDeclList(items, dtype);
    return;
  }
  const bool kQualified =
      quals.is_const || quals.is_static || quals.is_automatic;
  auto dtype = kQualified ? ParseDeclaredDataType() : ParseDataType();
  dtype.is_const = quals.is_const;
  if (dtype.kind != DataTypeKind::kImplicit || dtype.packed_dim_left ||
      dtype.signing_written || dtype.is_const) {
    ReportImplicitTypeWithoutVar(dtype, CurrentLoc(), diag_);
    ParseVarDeclList(items, dtype);
    return;
  }

  if (quals.is_automatic || quals.is_static) {
    diag_.Error(CurrentLoc(),
                "data_declaration without an explicit data type requires "
                "the 'var' keyword",
                Subclause("6.8"));
    Synchronize();
    return;
  }
  if (!CheckIdentifier()) {
    diag_.Error(CurrentLoc(), "unexpected token in module body",
                Subclause("23.2.4"));
    SynchronizeWithProgress();
    return;
  }
  ParseImplicitTypeOrInst(items);
}

}  // namespace delta
