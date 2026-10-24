// The data_declaration of a module, interface, program, checker or package
// body and of the compilation unit (A.2.1.3): the qualifiers that may open one,
// then its type and declarators, or, with no qualifier, the instantiation a
// leading name may begin instead. Parser::ParseModuleItem in
// src/parser/parser_items.cpp reaches these through ParseDataDeclItem when no
// other item opens at the current token; they stand in a file of their own to
// keep parser_items.cpp inside the limit assert-no-oversized-source-files
// enforces.

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
  // A.1.8 writes a checker's `rand` before the whole data_declaration, and
  // no other body's data_declaration takes one: A.1.4 and A.1.11 write it
  // bare.
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

// Each declarator of the declaration is marked as written after `var`, and its
// type as const where `is_const` says the declaration opened with `const`.
// A.2.2.1 lets the type be named through a package or class scope, which
// ParseDeclaredDataType reads past: ParseDataType took the unknown package
// name for the variable's, so `var P::T v;` stopped at the `::`.
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

// §6.8, footnote 14 of Syntax 6-3: a data declaration whose type is implicit,
// written as a sign, a packed range or nothing at all behind `const`, declares
// a variable only after `var`. A declaration that wrote `var` is read by
// ParseVarPrefixed instead, so one that reaches here wrote none.
static void ReportImplicitTypeWithoutVar(const DataType& dtype, SourceLoc loc,
                                         DiagEngine& diag) {
  if (dtype.kind != DataTypeKind::kImplicit) return;
  diag.Error(loc,
             "data_declaration without an explicit data type requires the "
             "'var' keyword",
             Subclause("6.8"));
}

// A.3.1 opens a gate_instantiation with its keyword and A.4.2 a
// case_generate_construct with `case`, so the `const` and the `static` that
// open a data_declaration (A.2.1.3) open neither. `automatic` is reported
// where it is read, as a lifetime outside a procedural context.
static void ReportQualifiersBeforeItem(const DataDeclQualifiers& quals,
                                       SourceLoc loc, const char* msg,
                                       Subclause subclause, DiagEngine& diag) {
  if (!quals.is_const && !quals.is_static) return;
  diag.Error(loc, msg, subclause);
}

// The type is read as ParseVarPrefixed reads a module item's. §8.5 puts no
// restriction on a property's data type, so an inline enumeration, structure
// or union and the package-scoped `pk::t` of §26.3 are read as a declaration's
// type is, and packed dimensions with no type before them are read as an
// implicit type. Footnote 14 of A.10 lets that implicit type stand only after
// `var`, and without it the property is reported as a module item is. A name
// followed by another is no implicit type but a type name the parse does not
// know, and the property's own parse reports what it makes of it.
DataType ParserDataDeclHelpers::ReadClassPropertyType(Parser& p) {
  bool has_var = p.Match(TokenKind::kKwVar);
  SourceLoc type_loc = p.CurrentLoc();
  DataType dtype;
  // A.2.2.1 counts a type_reference among the data types, which a property
  // writes after `var` as a module's variable does (§6.8).
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
    // ParseEnumType reads an enum's packed dimensions itself, so the second
    // reading finds none after one.
    auto dtype =
        Check(TokenKind::kKwEnum) ? ParseEnumType() : ParseStructOrUnionType();
    ParsePackedDims(dtype);
    dtype.is_const = quals.is_const;
    ParseVarDeclList(items, dtype);
    return;
  }
  // The qualifiers have taken every `const`, so none is left for
  // ParseDataType to read. Behind `const` or a lifetime the item is a
  // data_declaration (A.2.1.3), whose type may be named through a package or
  // class scope (A.2.2.1), as ParseDeclaredDataType reads it; read as an
  // implicit type, `const P::T v` and `static P::T v` were reported as wanting
  // `var`. With no qualifier a scoped name may open a checker instantiation
  // instead, which ParseImplicitTypeOrInst tells apart.
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
    // A stray block-closing keyword (e.g. endpackage from a misplaced package)
    // would otherwise make the enclosing body loop spin; recover with progress.
    SynchronizeWithProgress();
    return;
  }
  ParseImplicitTypeOrInst(items);
}

}  // namespace delta
