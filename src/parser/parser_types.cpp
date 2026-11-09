#include <algorithm>
#include <array>
#include <cstdint>
#include <format>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "parser/parser.h"
#include "parser/parser_data_decl_internal.h"

namespace delta {

bool IsNetTypeToken(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwWire:
    case TokenKind::kKwTri:
    case TokenKind::kKwTriand:
    case TokenKind::kKwTrior:
    case TokenKind::kKwTri0:
    case TokenKind::kKwTri1:
    case TokenKind::kKwTrireg:
    case TokenKind::kKwWand:
    case TokenKind::kKwWor:
    case TokenKind::kKwSupply0:
    case TokenKind::kKwSupply1:
    case TokenKind::kKwUwire:
      return true;
    default:
      return false;
  }
}

std::optional<DataTypeKind> TokenToTypeKind(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwLogic:
      return DataTypeKind::kLogic;
    case TokenKind::kKwReg:
      return DataTypeKind::kReg;
    case TokenKind::kKwBit:
      return DataTypeKind::kBit;
    case TokenKind::kKwByte:
      return DataTypeKind::kByte;
    case TokenKind::kKwShortint:
      return DataTypeKind::kShortint;
    case TokenKind::kKwInt:
      return DataTypeKind::kInt;
    case TokenKind::kKwLongint:
      return DataTypeKind::kLongint;
    case TokenKind::kKwInteger:
      return DataTypeKind::kInteger;
    case TokenKind::kKwReal:
      return DataTypeKind::kReal;
    case TokenKind::kKwShortreal:
      return DataTypeKind::kShortreal;
    case TokenKind::kKwRealtime:
      return DataTypeKind::kRealtime;
    case TokenKind::kKwTime:
      return DataTypeKind::kTime;
    case TokenKind::kKwString:
      return DataTypeKind::kString;
    case TokenKind::kKwEvent:
      return DataTypeKind::kEvent;
    case TokenKind::kKwVoid:
      return DataTypeKind::kVoid;
    case TokenKind::kKwChandle:
      return DataTypeKind::kChandle;
    case TokenKind::kKwWire:
      return DataTypeKind::kWire;
    case TokenKind::kKwTri:
      return DataTypeKind::kTri;
    case TokenKind::kKwTriand:
      return DataTypeKind::kTriand;
    case TokenKind::kKwTrior:
      return DataTypeKind::kTrior;
    case TokenKind::kKwTri0:
      return DataTypeKind::kTri0;
    case TokenKind::kKwTri1:
      return DataTypeKind::kTri1;
    case TokenKind::kKwTrireg:
      return DataTypeKind::kTrireg;
    case TokenKind::kKwWand:
      return DataTypeKind::kWand;
    case TokenKind::kKwWor:
      return DataTypeKind::kWor;
    case TokenKind::kKwSupply0:
      return DataTypeKind::kSupply0;
    case TokenKind::kKwSupply1:
      return DataTypeKind::kSupply1;
    case TokenKind::kKwUwire:
      return DataTypeKind::kUwire;
    default:
      return std::nullopt;
  }
}

static bool IsDefaultSigned(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
      return true;
    default:
      return false;
  }
}

static bool IsStrengthToken(TokenKind k) {
  switch (k) {
    case TokenKind::kKwSupply0:
    case TokenKind::kKwStrong0:
    case TokenKind::kKwPull0:
    case TokenKind::kKwWeak0:
    case TokenKind::kKwHighz0:
    case TokenKind::kKwSupply1:
    case TokenKind::kKwStrong1:
    case TokenKind::kKwPull1:
    case TokenKind::kKwWeak1:
    case TokenKind::kKwHighz1:
      return true;
    default:
      return false;
  }
}

uint8_t Parser::ParseChargeStrength() {
  if (!Check(TokenKind::kLParen)) return 0;
  auto saved = lexer_.SavePos();
  Consume();
  uint8_t result = 0;
  if (Match(TokenKind::kKwSmall)) {
    result = 1;
  } else if (Match(TokenKind::kKwMedium)) {
    result = 2;
  } else if (Match(TokenKind::kKwLarge)) {
    result = 4;
  }
  if (result != 0) {
    Expect(TokenKind::kRParen, Subclause("6.3.2.1"));
  } else {
    lexer_.RestorePos(saved);
  }
  return result;
}

DataType Parser::ParseVirtualInterfaceType() {
  DataType dtype;
  dtype.kind = DataTypeKind::kVirtualInterface;
  Match(TokenKind::kKwInterface);
  dtype.type_name = Expect(TokenKind::kIdentifier, Subclause("25.9")).text;
  if (Check(TokenKind::kHash)) {
    Consume();
    dtype.type_params = ParseTypeParamList();
  }
  if (Match(TokenKind::kDot)) {
    dtype.modport_name =
        Expect(TokenKind::kIdentifier, Subclause("25.9.2")).text;
  }
  return dtype;
}

static bool TakesPackedPart(DataTypeKind kind) {
  return kind == DataTypeKind::kBit || kind == DataTypeKind::kLogic ||
         kind == DataTypeKind::kReg;
}

bool Parser::AtUnsizedPackedDim(const DataType& dtype) {
  if (!in_dpi_import_formals_ || !TakesPackedPart(dtype.kind)) return false;
  if (!Check(TokenKind::kLBracket)) return false;
  auto saved = lexer_.SavePos();
  Consume();
  bool is_empty = Check(TokenKind::kRBracket);
  lexer_.RestorePos(saved);
  return is_empty;
}

void Parser::TakeUnsizedPackedDim(DataType& dtype) {
  Consume();
  Consume();
  dtype.has_unsized_packed_dim = true;
}

void Parser::ParsePackedDims(DataType& dtype) {
  if (AtUnsizedPackedDim(dtype)) {
    TakeUnsizedPackedDim(dtype);
  } else {
    if (!Check(TokenKind::kLBracket)) return;
    Consume();
    dtype.packed_dim_left = ParseExpr();
    Expect(TokenKind::kColon, Subclause("7.4.1"));
    dtype.packed_dim_right = ParseExpr();
    Expect(TokenKind::kRBracket, Subclause("7.4.1"));
  }

  while (Check(TokenKind::kLBracket)) {
    if (AtUnsizedPackedDim(dtype)) {
      if (dtype.has_unsized_packed_dim) return;
      TakeUnsizedPackedDim(dtype);
      continue;
    }
    auto saved = lexer_.SavePos();
    Consume();
    auto* left = ParseExpr();
    if (!Check(TokenKind::kColon)) {
      lexer_.RestorePos(saved);
      return;
    }
    Consume();
    auto* right = ParseExpr();
    Expect(TokenKind::kRBracket, Subclause("7.4.1"));
    dtype.extra_packed_dims.emplace_back(left, right);
  }
}

DataType Parser::ParseOneTypeParam() {
  bool named = Match(TokenKind::kDot);
  std::string_view arg_name;
  if (named) {
    arg_name = Expect(TokenKind::kIdentifier, Subclause("23.10.2.2")).text;
    Expect(TokenKind::kLParen, Subclause("23.10.2.2"));
  }
  DataType dt;
  if (!named || !Check(TokenKind::kRParen)) {
    if (!TryParseInlineAggregateType(dt)) dt = ParseDataType();
    if (dt.kind == DataTypeKind::kImplicit) {
      dt.type_ref_expr = ParseMinTypMaxExpr();
    }
  }
  if (named) {
    Expect(TokenKind::kRParen, Subclause("23.10.2.2"));
    dt.param_arg_name = arg_name;
  }
  return dt;
}

std::vector<DataType> Parser::ParseTypeParamList() {
  std::vector<DataType> result;
  Expect(TokenKind::kLParen, Subclause("23.10.2"));
  if (!Check(TokenKind::kRParen)) {
    result.push_back(ParseOneTypeParam());
    while (Match(TokenKind::kComma)) result.push_back(ParseOneTypeParam());
  }
  Expect(TokenKind::kRParen, Subclause("23.10.2"));
  return result;
}

void Parser::ParseNetStrength(DataType& dtype) {
  if (dtype.kind == DataTypeKind::kTrireg) {
    dtype.charge_strength = ParseChargeStrength();
    if (dtype.charge_strength != 0) return;
  } else {
    if (!dtype.is_net || !Check(TokenKind::kLParen)) return;
    SourceLoc charge_loc = CurrentLoc();
    if (ParseChargeStrength() != 0) {
      diag_.Error(charge_loc,
                  "charge strength can only be used with trireg nets",
                  Subclause("6.3.2.1"));
      return;
    }
  }
  if (!Check(TokenKind::kLParen)) return;
  auto saved = lexer_.SavePos();
  SourceLoc drive_loc = CurrentLoc();
  Consume();
  if (IsStrengthToken(CurrentToken().kind)) {
    ParseDriveStrength(dtype.drive_strength0, dtype.drive_strength1);
    Expect(TokenKind::kRParen, Subclause("6.3.2.2"));
    if (dtype.kind == DataTypeKind::kNamed) {
      diag_.Error(drive_loc,
                  "a net of a user-defined nettype takes no drive strength",
                  Subclause("6.7"));
    }
  } else {
    lexer_.RestorePos(saved);
  }
}

DataType Parser::ParseNamedType() {
  DataType dtype;
  dtype.kind = DataTypeKind::kNamed;
  dtype.type_name = Consume().text;

  bool assignment_written = false;
  if (Check(TokenKind::kHash) && known_nettypes_.count(dtype.type_name) == 0) {
    Consume();
    dtype.type_params = ParseTypeParamList();
    assignment_written = true;
  }

  while (Check(TokenKind::kColonColon)) {
    auto saved = lexer_.SavePos();
    Consume();
    if (!CheckIdentifier()) {
      lexer_.RestorePos(saved);
      break;
    }
    if (!dtype.scope_name.empty())
      dtype.outer_scope_names.push_back(dtype.scope_name);
    dtype.scope_name = dtype.type_name;
    dtype.scope_param_assignment_written = assignment_written;
    dtype.type_name = Consume().text;
    assignment_written = Check(TokenKind::kHash);
    if (assignment_written) {
      Consume();
      dtype.type_params = ParseTypeParamList();
    }
  }
  return dtype;
}

static void ApplyNetInfo(DataType& inner, const DataType& net) {
  inner.is_net = true;
  inner.net_keyword = net.net_keyword;
  inner.is_vectored = net.is_vectored;
  inner.is_scalared = net.is_scalared;
  inner.drive_strength0 = net.drive_strength0;
  inner.drive_strength1 = net.drive_strength1;
  inner.charge_strength = net.charge_strength;
}

bool Parser::TryParseNetDataType(DataType& dtype, bool has_intervening) {
  if (!has_intervening && CurrentToken().kind == TokenKind::kKwReg) {
    diag_.Error(CurrentLoc(),
                "'reg' cannot come right after a net type keyword",
                Subclause("6.7.1"));
    Consume();
    return false;
  }

  if (Check(TokenKind::kIdentifier) &&
      (known_types_.count(CurrentToken().text) != 0 || AtScopedTypeName())) {
    auto inner = ParseNamedType();
    ParsePackedDims(inner);
    ApplyNetInfo(inner, dtype);
    dtype = inner;
    return true;
  }

  if (Check(TokenKind::kKwStruct) || Check(TokenKind::kKwUnion)) {
    auto inner = ParseStructOrUnionType();
    ParsePackedDims(inner);
    ApplyNetInfo(inner, dtype);
    dtype = inner;
    return true;
  }

  if (Check(TokenKind::kKwType)) {
    Consume();
    Expect(TokenKind::kLParen, Subclause("6.23"));
    dtype.type_ref_expr = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("6.23"));
    return true;
  }

  if (Check(TokenKind::kKwEnum)) {
    auto inner = ParseEnumType();
    ApplyNetInfo(inner, dtype);
    dtype = inner;
    return true;
  }

  auto inner_kind = TokenToTypeKind(CurrentToken().kind);
  if (inner_kind && !IsNetTypeToken(CurrentToken().kind)) {
    if (dtype.kind != DataTypeKind::kTrireg) dtype.kind = *inner_kind;
    dtype.is_signed = IsDefaultSigned(*inner_kind);
    Consume();
  }
  return false;
}

bool Parser::AtDataTypeOrVoid() {
  if (Check(TokenKind::kIdentifier)) {
    return known_types_.count(CurrentToken().text) != 0;
  }
  auto tk = CurrentToken().kind;
  switch (tk) {
    case TokenKind::kKwStruct:
    case TokenKind::kKwUnion:
    case TokenKind::kKwEnum:
    case TokenKind::kKwVirtual:
    case TokenKind::kKwType:
    case TokenKind::kKwConst:
    case TokenKind::kKwSigned:
    case TokenKind::kKwUnsigned:
    case TokenKind::kLBracket:
      return true;
    default:
      break;
  }
  return TokenToTypeKind(tk).has_value();
}

DataType Parser::ParseDeclaredDataType() {
  bool scoped = false;
  if (Check(TokenKind::kIdentifier) &&
      known_types_.count(CurrentToken().text) == 0) {
    auto saved = lexer_.SavePos();
    Consume();
    scoped = Match(TokenKind::kColonColon) && CheckIdentifier();
    if (scoped) {
      Consume();
      scoped = !Check(TokenKind::kLParen);
    }
    lexer_.RestorePos(saved);
  }
  if (!scoped) return ParseDataType();
  DataType dtype = ParseNamedType();
  ParsePackedDims(dtype);
  return dtype;
}

void Parser::ParseVectoredScalared(DataType& dtype) {
  if (dtype.is_net) {
    dtype.is_vectored = Match(TokenKind::kKwVectored);
    if (!dtype.is_vectored) dtype.is_scalared = Match(TokenKind::kKwScalared);
    return;
  }
  if (!Check(TokenKind::kKwVectored) && !Check(TokenKind::kKwScalared)) return;
  Token tok = CurrentToken();
  diag_.Error(tok.loc,
              std::format("'{}' shall be used in a vector net declaration and "
                          "'{}' declares no net",
                          tok.text, dtype.type_name),
              Subclause("6.9.2"));
  Consume();
}

DataType Parser::ParseDataType() {
  DataType dtype;

  if (Match(TokenKind::kKwConst)) {
    dtype.is_const = true;
  }

  if (Check(TokenKind::kKwVirtual)) {
    Consume();
    return ParseVirtualInterfaceType();
  }

  bool is_named = (Check(TokenKind::kIdentifier) &&
                   known_types_.count(CurrentToken().text) != 0) ||
                  ParserDataDeclHelpers::AtUnitScopedTypeName(*this);
  if (is_named) {
    auto named = ParseNamedType();
    named.is_const = dtype.is_const;
    ParsePackedDims(named);
    return named;
  }

  if (Check(TokenKind::kKwSigned) || Check(TokenKind::kKwUnsigned)) {
    dtype.is_signed = Check(TokenKind::kKwSigned);
    dtype.signing_written = true;
    Consume();
    ParsePackedDims(dtype);
    return dtype;
  }

  auto tok_kind = CurrentToken().kind;
  auto kind = TokenToTypeKind(tok_kind);
  if (!kind) return dtype;
  dtype.kind = *kind;
  dtype.is_net = IsNetTypeToken(tok_kind);
  if (dtype.is_net) dtype.net_keyword = dtype.kind;
  dtype.type_name = CurrentToken().text;
  dtype.is_signed = IsDefaultSigned(dtype.kind);
  Consume();

  ParseNetStrength(dtype);
  ParseVectoredScalared(dtype);

  bool has_intervening = dtype.drive_strength0 != 0 ||
                         dtype.charge_strength != 0 || dtype.is_vectored ||
                         dtype.is_scalared;
  if (dtype.is_net && TryParseNetDataType(dtype, has_intervening)) return dtype;

  ParserDataDeclHelpers::ReadSigning(*this, dtype);
  ParsePackedDims(dtype);
  return dtype;
}

bool ParserDataDeclHelpers::IsIntegerAtomKind(DataTypeKind kind) {
  static constexpr std::array kAtoms = {
      DataTypeKind::kByte,    DataTypeKind::kShortint, DataTypeKind::kInt,
      DataTypeKind::kLongint, DataTypeKind::kInteger,  DataTypeKind::kTime};
  return std::ranges::find(kAtoms, kind) != kAtoms.end();
}

bool ParserDataDeclHelpers::IsIntegerVectorKind(DataTypeKind kind) {
  static constexpr std::array kVectors = {
      DataTypeKind::kBit, DataTypeKind::kLogic, DataTypeKind::kReg};
  return std::ranges::find(kVectors, kind) != kVectors.end();
}

void ParserDataDeclHelpers::ReadSigning(Parser& p, DataType& dtype) {
  if (!p.Check(TokenKind::kKwSigned) && !p.Check(TokenKind::kKwUnsigned)) {
    return;
  }
  Token signing = p.Consume();
  bool net_alone = dtype.is_net && dtype.kind == dtype.net_keyword;
  if (net_alone || IsIntegerAtomKind(dtype.kind) ||
      IsIntegerVectorKind(dtype.kind)) {
    dtype.is_signed = signing.kind == TokenKind::kKwSigned;
    return;
  }
  p.diag_.Error(signing.loc,
                "only an integer vector or integer atom type takes a signing",
                Subclause("A.2.2.1"));
}

void Parser::ParseUnpackedDims(std::vector<Expr*>& dims) {
  while (Check(TokenKind::kLBracket)) {
    Consume();
    if (Match(TokenKind::kRBracket)) {
      dims.push_back(nullptr);
      continue;
    }
    if (Check(TokenKind::kDollar)) {
      SourceLoc dollar_loc = CurrentLoc();
      Consume();
      auto* dim = arena_.Create<Expr>();
      dim->kind = ExprKind::kIdentifier;
      dim->range.start = dollar_loc;
      dim->text = "$";
      if (Match(TokenKind::kColon)) {
        dim->rhs = ParseExpr();
      }
      dims.push_back(dim);
      Expect(TokenKind::kRBracket, Subclause("7.10"));
      continue;
    }
    if (Check(TokenKind::kStar)) {
      SourceLoc star_loc = CurrentLoc();
      Consume();
      auto* dim = arena_.Create<Expr>();
      dim->kind = ExprKind::kIdentifier;
      dim->range.start = star_loc;
      dim->text = "*";
      dims.push_back(dim);
      Expect(TokenKind::kRBracket, Subclause("7.8.1"));
      continue;
    }

    if (ParserDataDeclHelpers::AtIndexType(*this)) {
      dims.push_back(ParseAssocIndexDim());
      Expect(TokenKind::kRBracket, Subclause("7.8"));
      continue;
    }
    auto* expr = ParseExpr();
    if (Match(TokenKind::kColon)) {
      auto* range = arena_.Create<Expr>();
      range->kind = ExprKind::kBinary;
      range->op = TokenKind::kColon;
      range->range.start = expr->range.start;
      range->lhs = expr;
      range->rhs = ParseExpr();
      dims.push_back(range);
    } else {
      dims.push_back(expr);
    }
    Expect(TokenKind::kRBracket, Subclause("7.4.2"));
  }
}

void Parser::ParseVarDeclList(std::vector<ModuleItem*>& items,
                              const DataType& dtype) {
  Expr* nd1 = nullptr;
  Expr* nd2 = nullptr;
  Expr* nd3 = nullptr;
  bool nettype_named = dtype.kind == DataTypeKind::kNamed &&
                       known_nettypes_.count(dtype.type_name) != 0;
  Subclause subclause(dtype.is_net ? "6.7" : "6.8");
  if (nettype_named) {
    DataType as_net = dtype;
    as_net.is_net = true;
    ParseNetStrength(as_net);
  }
  if (dtype.is_net || nettype_named) {
    ParseGateDelay(nd1, nd2, nd3);
    ReportDriveStrengthAfterDelay(nd1);
  }
  const std::string_view kFsmEnum = lexer_.ClaimFsmEnumPragma(CurrentLoc());
  bool first = true;
  do {
    auto* item = arena_.Create<ModuleItem>();
    item->kind =
        dtype.is_net ? ModuleItemKind::kNetDecl : ModuleItemKind::kVarDecl;
    item->fsm_enum = kFsmEnum;
    item->first_in_decl_list = first;
    first = false;
    item->loc = CurrentLoc();
    item->data_type = dtype;
    item->drive_strength0 = dtype.drive_strength0;
    item->drive_strength1 = dtype.drive_strength1;
    item->net_delay = nd1;
    item->net_delay_fall = nd2;
    item->net_delay_decay = nd3;
    item->name = ExpectIdentifier(subclause).text;
    ParseUnpackedDims(item->unpacked_dims);
    if (Match(TokenKind::kEq)) {
      item->init_expr = ParseExpr();
    }
    items.push_back(item);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon, subclause);
}

static bool IsForwardTypeParamToken(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwEnum:
    case TokenKind::kKwStruct:
    case TokenKind::kKwUnion:
    case TokenKind::kKwClass:
    case TokenKind::kKwInterface:
      return true;
    default:
      return false;
  }
}

static DataTypeKind ForwardTypeKindForToken(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwEnum:
      return DataTypeKind::kEnum;
    case TokenKind::kKwStruct:
      return DataTypeKind::kStruct;
    case TokenKind::kKwUnion:
      return DataTypeKind::kUnion;
    case TokenKind::kKwClass:
      return DataTypeKind::kNamed;
    default:
      return DataTypeKind::kImplicit;
  }
}

DataTypeKind Parser::ParseTypeParamRestriction() {
  if (!IsForwardTypeParamToken(CurrentToken().kind)) {
    return DataTypeKind::kImplicit;
  }
  if (Match(TokenKind::kKwInterface)) {
    Expect(TokenKind::kKwClass, Subclause("6.20.3"));
    return DataTypeKind::kVoid;
  }
  const DataTypeKind kRestriction =
      ForwardTypeKindForToken(CurrentToken().kind);
  Consume();
  return kRestriction;
}

DataType Parser::ParseTypeAssignmentValue() {
  if (!Check(TokenKind::kIdentifier) || !AtScopedTypeName())
    return ParseDataType();
  DataType named = ParseNamedType();
  ParsePackedDims(named);
  return named;
}

void Parser::ParseTypeParamDecl(std::vector<ModuleItem*>& items, SourceLoc loc,
                                bool localparam) {
  const DataTypeKind kRestriction = ParseTypeParamRestriction();

  do {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kParamDecl;
    item->is_localparam = localparam;
    item->loc = loc;
    item->data_type.kind = DataTypeKind::kVoid;
    item->forward_type_kind = kRestriction;
    auto name_tok = Expect(TokenKind::kIdentifier, Subclause("6.20.3"));
    item->name = name_tok.text;
    bool has_default = false;
    if (Match(TokenKind::kEq)) {
      has_default = true;
      auto dtype = ParseTypeAssignmentValue();
      if (dtype.kind != DataTypeKind::kImplicit) {
        item->typedef_type = dtype;
      } else {
        item->init_expr = ParseExpr();
      }
    }

    if (!has_default) {
      diag_.Error(name_tok.loc,
                  std::format("type parameter '{}' outside a parameter port "
                              "list must have a default type",
                              name_tok.text),
                  Subclause("6.20.1"));
    }
    known_types_.insert(item->name);
    items.push_back(item);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon, Subclause("6.20.3"));
}

void Parser::ParseParamDecl(std::vector<ModuleItem*>& items) {
  auto loc = CurrentLoc();
  bool localparam = Check(TokenKind::kKwLocalparam);
  Consume();

  if (ForceLocalparam()) localparam = true;

  if (!ParserDataDeclHelpers::AtTypeReference(*this) &&
      Match(TokenKind::kKwType)) {
    ParseTypeParamDecl(items, loc, localparam);
    return;
  }
  DataType dtype;
  if (!ParserDataDeclHelpers::ReadTypeReference(*this, dtype) &&
      !TryParseInlineAggregateType(dtype)) {
    dtype = ParseDeclaredDataType();
    ParseImplicitParamRange(dtype);
  }
  const std::string_view kFsmEnum = lexer_.ClaimFsmEnumPragma(CurrentLoc());

  bool first = true;
  do {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kParamDecl;
    item->is_localparam = localparam;
    item->fsm_enum = kFsmEnum;
    item->loc = loc;
    item->data_type = dtype;
    item->first_in_decl_list = std::exchange(first, false);
    item->name = Expect(TokenKind::kIdentifier, Subclause("6.20.1")).text;
    ParseUnpackedDims(item->unpacked_dims);
    if (Match(TokenKind::kEq)) {
      item->init_expr = ParseMinTypMaxExpr();
    } else {
      diag_.Error(item->loc, "parameter declaration requires a default value",
                  Subclause("6.20.1"));
    }
    items.push_back(item);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon, Subclause("6.20.1"));
}

void Parser::ParseImplicitParamRange(DataType& dtype) {
  if (dtype.kind == DataTypeKind::kImplicit) ParsePackedDims(dtype);
}

bool ParserDataDeclHelpers::ReadTypeReference(Parser& p, DataType& dtype) {
  if (!p.Check(TokenKind::kKwType)) return false;
  p.Consume();
  p.Expect(TokenKind::kLParen, Subclause("6.23"));
  dtype.type_ref_expr = p.ParseExpr();
  p.Expect(TokenKind::kRParen, Subclause("6.23"));
  return true;
}

bool ParserDataDeclHelpers::ReadKeyedTypeReference(Parser& p, DataType& dtype,
                                                   bool has_var, bool is_port) {
  if (!has_var && p.Check(TokenKind::kKwType)) {
    p.diag_.Error(p.CurrentLoc(),
                  is_port ? "type_reference in a port declaration must be "
                            "preceded by the 'var' keyword or a net type "
                            "keyword"
                          : "type_reference in a variable declaration must be "
                            "preceded by the 'var' keyword",
                  Subclause("6.23"));
  }
  return ReadTypeReference(p, dtype);
}

bool ParserDataDeclHelpers::AtTypeReference(Parser& p) {
  if (!p.Check(TokenKind::kKwType)) return false;
  auto saved = p.lexer_.SavePos();
  p.Consume();
  bool opens = p.Check(TokenKind::kLParen);
  p.lexer_.RestorePos(saved);
  return opens;
}

bool Parser::TryParseTypeRef(std::vector<ModuleItem*>& items) {
  DataType dtype;
  if (!ParserDataDeclHelpers::ReadTypeReference(*this, dtype)) return false;
  ParseVarDeclList(items, dtype);
  return true;
}

}  // namespace delta
