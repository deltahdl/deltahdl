#include <format>
#include <optional>

#include "parser/parser.h"

namespace delta {

static bool IsNetTypeToken(TokenKind tk) {
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

static std::optional<DataTypeKind> TokenToTypeKind(TokenKind tk) {
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
    Expect(TokenKind::kRParen);
  } else {
    lexer_.RestorePos(saved);
  }
  return result;
}

DataType Parser::ParseVirtualInterfaceType() {
  DataType dtype;
  dtype.kind = DataTypeKind::kVirtualInterface;
  Match(TokenKind::kKwInterface);
  dtype.type_name = Expect(TokenKind::kIdentifier).text;
  if (Check(TokenKind::kHash)) {
    Consume();
    dtype.type_params = ParseTypeParamList();
  }
  if (Match(TokenKind::kDot)) {
    dtype.modport_name = Expect(TokenKind::kIdentifier).text;
  }
  return dtype;
}

void Parser::ParsePackedDims(DataType& dtype) {
  if (!Check(TokenKind::kLBracket)) return;
  Consume();
  dtype.packed_dim_left = ParseExpr();
  Expect(TokenKind::kColon);
  dtype.packed_dim_right = ParseExpr();
  Expect(TokenKind::kRBracket);

  while (Check(TokenKind::kLBracket)) {
    auto saved = lexer_.SavePos();
    Consume();
    auto* left = ParseExpr();
    if (!Check(TokenKind::kColon)) {
      lexer_.RestorePos(saved);
      return;
    }
    Consume();
    auto* right = ParseExpr();
    Expect(TokenKind::kRBracket);
    dtype.extra_packed_dims.emplace_back(left, right);
  }
}

std::vector<DataType> Parser::ParseTypeParamList() {
  std::vector<DataType> result;
  Expect(TokenKind::kLParen);
  if (!Check(TokenKind::kRParen)) {
    auto dt = ParseDataType();
    if (dt.kind == DataTypeKind::kImplicit) {
      dt.type_ref_expr = ParseExpr();
    }
    result.push_back(dt);
    while (Match(TokenKind::kComma)) {
      dt = ParseDataType();
      if (dt.kind == DataTypeKind::kImplicit) {
        dt.type_ref_expr = ParseExpr();
      }
      result.push_back(dt);
    }
  }
  Expect(TokenKind::kRParen);
  return result;
}

void Parser::ParseNetStrength(DataType& dtype) {
  if (dtype.kind == DataTypeKind::kTrireg) {
    dtype.charge_strength = ParseChargeStrength();
    return;
  }
  if (!dtype.is_net || !Check(TokenKind::kLParen)) return;
  auto saved = lexer_.SavePos();
  Consume();
  if (IsStrengthToken(CurrentToken().kind)) {
    ParseDriveStrength(dtype.drive_strength0, dtype.drive_strength1);
    Expect(TokenKind::kRParen);
  } else {
    lexer_.RestorePos(saved);
  }
}

DataType Parser::ParseNamedType() {
  DataType dtype;
  dtype.kind = DataTypeKind::kNamed;
  dtype.type_name = Consume().text;

  if (Check(TokenKind::kHash)) {
    Consume();
    dtype.type_params = ParseTypeParamList();
  }

  while (Check(TokenKind::kColonColon)) {
    auto saved = lexer_.SavePos();
    Consume();
    if (!CheckIdentifier()) {
      lexer_.RestorePos(saved);
      break;
    }
    dtype.scope_name = dtype.type_name;
    dtype.type_name = Consume().text;
    if (Check(TokenKind::kHash)) {
      Consume();
      dtype.type_params = ParseTypeParamList();
    }
  }
  return dtype;
}

static void ApplyNetInfo(DataType& inner, const DataType& net) {
  inner.is_net = true;
  inner.is_vectored = net.is_vectored;
  inner.is_scalared = net.is_scalared;
  inner.drive_strength0 = net.drive_strength0;
  inner.drive_strength1 = net.drive_strength1;
  inner.charge_strength = net.charge_strength;
}

bool Parser::TryParseNetDataType(DataType& dtype, bool has_intervening) {
  if (!has_intervening && CurrentToken().kind == TokenKind::kKwReg) {
    diag_.Error(CurrentLoc(),
                "net type keyword shall not be followed directly by 'reg'");
    Consume();
    return false;
  }

  if (Check(TokenKind::kIdentifier) &&
      known_types_.count(CurrentToken().text) != 0) {
    auto inner = ParseNamedType();
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
    Expect(TokenKind::kLParen);
    dtype.type_ref_expr = ParseExpr();
    Expect(TokenKind::kRParen);
    return true;
  }

  if (Check(TokenKind::kKwEnum)) {
    auto inner = ParseEnumType();
    ParsePackedDims(inner);
    ApplyNetInfo(inner, dtype);
    dtype = inner;
    return true;
  }

  auto inner_kind = TokenToTypeKind(CurrentToken().kind);
  if (inner_kind && !IsNetTypeToken(CurrentToken().kind)) {
    dtype.kind = *inner_kind;
    dtype.is_signed = IsDefaultSigned(dtype.kind);
    Consume();
  }
  return false;
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

  if (Check(TokenKind::kIdentifier)) {
    auto named = ParseNamedType();
    named.is_const = dtype.is_const;
    ParsePackedDims(named);
    return named;
  }

  if (Check(TokenKind::kKwSigned) || Check(TokenKind::kKwUnsigned)) {
    dtype.is_signed = Check(TokenKind::kKwSigned);
    Consume();
    ParsePackedDims(dtype);
    return dtype;
  }

  auto tok_kind = CurrentToken().kind;
  auto kind = TokenToTypeKind(tok_kind);
  if (!kind) return dtype;
  dtype.kind = *kind;
  dtype.is_net = IsNetTypeToken(tok_kind);

  dtype.is_signed = IsDefaultSigned(dtype.kind);
  Consume();

  ParseNetStrength(dtype);

  dtype.is_vectored = dtype.is_net && Match(TokenKind::kKwVectored);
  if (dtype.is_net && !dtype.is_vectored) {
    dtype.is_scalared = Match(TokenKind::kKwScalared);
  }

  bool has_intervening = dtype.drive_strength0 != 0 ||
                         dtype.charge_strength != 0 || dtype.is_vectored ||
                         dtype.is_scalared;
  if (dtype.is_net && TryParseNetDataType(dtype, has_intervening)) return dtype;

  if (Match(TokenKind::kKwSigned)) {
    dtype.is_signed = true;
  } else if (Match(TokenKind::kKwUnsigned)) {
    dtype.is_signed = false;
  }

  ParsePackedDims(dtype);
  return dtype;
}

static bool IsAssocIndexType(TokenKind tk) {
  return TokenToTypeKind(tk).has_value() && tk != TokenKind::kKwVoid;
}

void Parser::ParseUnpackedDims(std::vector<Expr*>& dims) {
  while (Check(TokenKind::kLBracket)) {
    Consume();
    if (Match(TokenKind::kRBracket)) {
      dims.push_back(nullptr);
      continue;
    }
    if (Match(TokenKind::kDollar)) {
      auto* dim = arena_.Create<Expr>();
      dim->kind = ExprKind::kIdentifier;
      dim->text = "$";
      if (Match(TokenKind::kColon)) {
        dim->rhs = ParseExpr();
      }
      dims.push_back(dim);
      Expect(TokenKind::kRBracket);
      continue;
    }
    if (Match(TokenKind::kStar)) {
      auto* dim = arena_.Create<Expr>();
      dim->kind = ExprKind::kIdentifier;
      dim->text = "*";
      dims.push_back(dim);
      Expect(TokenKind::kRBracket);
      continue;
    }

    if (IsAssocIndexType(CurrentToken().kind)) {
      auto* dim = arena_.Create<Expr>();
      dim->kind = ExprKind::kIdentifier;
      dim->text = Consume().text;
      dims.push_back(dim);
      Expect(TokenKind::kRBracket);
      continue;
    }
    auto* expr = ParseExpr();
    if (Match(TokenKind::kColon)) {
      auto* range = arena_.Create<Expr>();
      range->kind = ExprKind::kBinary;
      range->op = TokenKind::kColon;
      range->lhs = expr;
      range->rhs = ParseExpr();
      dims.push_back(range);
    } else {
      dims.push_back(expr);
    }
    Expect(TokenKind::kRBracket);
  }
}

void Parser::ParseVarDeclList(std::vector<ModuleItem*>& items,
                              const DataType& dtype) {
  DataType actual_dtype = dtype;

  // Handle "const var type" case: if we have const with implicit type,
  // the actual type follows the var keyword.
  if (actual_dtype.kind == DataTypeKind::kImplicit && actual_dtype.is_const &&
      Check(TokenKind::kKwVar)) {
    Consume();  // consume "var"
    actual_dtype = ParseDataType();
    actual_dtype.is_const = true;  // preserve const flag
    if (actual_dtype.kind == DataTypeKind::kImplicit &&
        Check(TokenKind::kLBracket)) {
      ParsePackedDims(actual_dtype);
    }
  }

  Expr* nd1 = nullptr;
  Expr* nd2 = nullptr;
  Expr* nd3 = nullptr;
  bool nettype_named = actual_dtype.kind == DataTypeKind::kNamed &&
                       known_nettypes_.count(actual_dtype.type_name) != 0;
  if (actual_dtype.is_net || nettype_named) ParseGateDelay(nd1, nd2, nd3);
  do {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = actual_dtype.is_net ? ModuleItemKind::kNetDecl
                                     : ModuleItemKind::kVarDecl;
    item->loc = CurrentLoc();
    item->data_type = actual_dtype;
    item->drive_strength0 = actual_dtype.drive_strength0;
    item->drive_strength1 = actual_dtype.drive_strength1;
    item->net_delay = nd1;
    item->net_delay_fall = nd2;
    item->net_delay_decay = nd3;
    item->name = ExpectIdentifier().text;
    ParseUnpackedDims(item->unpacked_dims);
    if (Match(TokenKind::kEq)) {
      item->init_expr = ParseExpr();
    }
    items.push_back(item);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
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

void Parser::ParseTypeParamDecl(std::vector<ModuleItem*>& items, SourceLoc loc,
                                bool localparam) {
  DataTypeKind fwd = DataTypeKind::kImplicit;
  if (IsForwardTypeParamToken(CurrentToken().kind)) {
    if (Match(TokenKind::kKwInterface)) {
      Expect(TokenKind::kKwClass);
      fwd = DataTypeKind::kVoid;
    } else {
      fwd = ForwardTypeKindForToken(CurrentToken().kind);
      Consume();
    }
  }

  do {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kParamDecl;
    item->is_localparam = localparam;
    item->loc = loc;
    item->data_type.kind = DataTypeKind::kVoid;
    item->forward_type_kind = fwd;
    auto name_tok = Expect(TokenKind::kIdentifier);
    item->name = name_tok.text;
    bool has_default = false;
    if (Match(TokenKind::kEq)) {
      has_default = true;
      auto dtype = ParseDataType();
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
                              name_tok.text));
    }
    known_types_.insert(item->name);
    items.push_back(item);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
}

void Parser::ParseParamDecl(std::vector<ModuleItem*>& items) {
  auto loc = CurrentLoc();
  bool localparam = Check(TokenKind::kKwLocalparam);
  Consume();

  if (ForceLocalparam()) localparam = true;

  if (Match(TokenKind::kKwType)) {
    ParseTypeParamDecl(items, loc, localparam);
    return;
  }
  DataType dtype = ParseDataType();
  ParseImplicitParamRange(dtype);

  do {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kParamDecl;
    item->is_localparam = localparam;
    item->loc = loc;
    item->data_type = dtype;
    item->name = Expect(TokenKind::kIdentifier).text;
    ParseUnpackedDims(item->unpacked_dims);
    if (Match(TokenKind::kEq)) {
      item->init_expr = ParseExpr();
    } else {
      // §6.20.1 fn22: omitting the value is legal only in a
      // parameter_port_list (a separate parse path), not here.
      diag_.Error(item->loc, "parameter declaration requires a default value");
    }
    items.push_back(item);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
}

// §6.20.2 / §A.2.1.1: a value parameter may carry a packed range with no
// explicit data type (e.g. `parameter [7:0] P`). ParseDataType does not consume
// a bare leading range, so do it here. The type stays implicit -- it is not an
// explicit `logic` -- and its width comes from the range.
void Parser::ParseImplicitParamRange(DataType& dtype) {
  if (dtype.kind != DataTypeKind::kImplicit || !Check(TokenKind::kLBracket)) {
    return;
  }
  Consume();
  dtype.packed_dim_left = ParseExpr();
  Expect(TokenKind::kColon);
  dtype.packed_dim_right = ParseExpr();
  Expect(TokenKind::kRBracket);
}

bool Parser::TryParseTypeRef(std::vector<ModuleItem*>& items) {
  if (!Check(TokenKind::kKwType)) return false;
  Consume();
  Expect(TokenKind::kLParen);
  auto* type_expr = ParseExpr();
  Expect(TokenKind::kRParen);
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kVarDecl;
  item->loc = CurrentLoc();
  item->data_type.type_ref_expr = type_expr;
  item->name = ExpectIdentifier().text;
  ParseUnpackedDims(item->unpacked_dims);
  Expect(TokenKind::kSemicolon);
  items.push_back(item);
  return true;
}

}  // namespace delta
