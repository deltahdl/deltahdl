#include <optional>

#include "parser/parser.h"

namespace delta {

// --- Types ---

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

// §6.11.3 Table 6-8: Types that are signed by default.
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

// §6.3.2.2: Check if a token is a drive strength keyword.
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
  Consume();  // '('
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

// Virtual interface type: virtual [interface] ifc [#(params)] [.modport] (§25.9)
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

// Parse packed dimensions: [a:b] ([c:d] ...)* (§7.4.1)
void Parser::ParsePackedDims(DataType& dtype) {
  if (!Check(TokenKind::kLBracket)) return;
  Consume();
  dtype.packed_dim_left = ParseExpr();
  Expect(TokenKind::kColon);
  dtype.packed_dim_right = ParseExpr();
  Expect(TokenKind::kRBracket);
  // Additional packed dimensions: bit [3:0] [7:0] ...
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

// §8.25: parse type parameter list — each element is a type or expression.
std::vector<DataType> Parser::ParseTypeParamList() {
  std::vector<DataType> result;
  Expect(TokenKind::kLParen);
  if (!Check(TokenKind::kRParen)) {
    auto dt = ParseDataType();
    if (dt.kind == DataTypeKind::kImplicit) {
      ParseExpr();
    }
    result.push_back(dt);
    while (Match(TokenKind::kComma)) {
      dt = ParseDataType();
      if (dt.kind == DataTypeKind::kImplicit) {
        ParseExpr();
      }
      result.push_back(dt);
    }
  }
  Expect(TokenKind::kRParen);
  return result;
}

// §6.3.2: Parse charge strength (trireg) or drive strength (other nets).
void Parser::ParseNetStrength(DataType& dtype) {
  if (dtype.kind == DataTypeKind::kTrireg) {
    dtype.charge_strength = ParseChargeStrength();
    return;
  }
  if (!dtype.is_net || !Check(TokenKind::kLParen)) return;
  auto saved = lexer_.SavePos();
  Consume();  // '('
  if (IsStrengthToken(CurrentToken().kind)) {
    ParseDriveStrength(dtype.drive_strength0, dtype.drive_strength1);
    Expect(TokenKind::kRParen);
  } else {
    lexer_.RestorePos(saved);
  }
}

// §6.25/§8.26.3: Parse a named type with optional #(params) and :: scoping.
DataType Parser::ParseNamedType() {
  DataType dtype;
  dtype.kind = DataTypeKind::kNamed;
  dtype.type_name = Consume().text;
  // §6.25/§8.25: parameterized class type params come before ::
  if (Check(TokenKind::kHash)) {
    Consume();
    dtype.type_params = ParseTypeParamList();
  }
  // §8.26.3 scope-resolved types: class_name::type_name
  while (Check(TokenKind::kColonColon)) {
    auto saved = lexer_.SavePos();
    Consume();  // ::
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

// Copy net-specific fields from outer net declaration into inner data type.
static void ApplyNetInfo(DataType& inner, const DataType& net) {
  inner.is_net = true;
  inner.is_vectored = net.is_vectored;
  inner.is_scalared = net.is_scalared;
  inner.drive_strength0 = net.drive_strength0;
  inner.drive_strength1 = net.drive_strength1;
  inner.charge_strength = net.charge_strength;
}

// §6.7.1: Try to parse explicit data_type after net keyword.
// Returns true if an explicit type was parsed and merged into dtype.
// Returns false for implicit_data_type (caller continues with signing + dims).
bool Parser::TryParseNetDataType(DataType& dtype, bool has_intervening) {
  // §6.7.1: A net type keyword shall not be followed directly by 'reg'.
  if (!has_intervening && CurrentToken().kind == TokenKind::kKwReg) {
    diag_.Error(CurrentLoc(),
                "net type keyword shall not be followed directly by 'reg'");
    Consume();
    return false;
  }
  // Named type (user-defined): wire addressT w1;
  if (CurrentToken().Is(TokenKind::kIdentifier) &&
      known_types_.count(CurrentToken().text) != 0) {
    auto inner = ParseNamedType();
    ApplyNetInfo(inner, dtype);
    dtype = inner;
    return true;
  }
  // Struct/union type: wire struct packed { ... } [dims] memsig;
  if (Check(TokenKind::kKwStruct) || Check(TokenKind::kKwUnion)) {
    auto inner = ParseStructOrUnionType();
    ParsePackedDims(inner);
    ApplyNetInfo(inner, dtype);
    dtype = inner;
    return true;
  }
  // Enum type: wire enum { ... } [dims] e;
  if (Check(TokenKind::kKwEnum)) {
    auto inner = ParseEnumType();
    ParsePackedDims(inner);
    ApplyNetInfo(inner, dtype);
    dtype = inner;
    return true;
  }
  // Non-net built-in type: wire logic [7:0] w; wire bit [3:0] b;
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

  bool is_named = CurrentToken().Is(TokenKind::kIdentifier) &&
                  known_types_.count(CurrentToken().text) != 0;
  if (is_named) {
    auto named = ParseNamedType();
    named.is_const = dtype.is_const;
    ParsePackedDims(named);
    return named;
  }

  // A.2.2.1: implicit_data_type ::= [signing] {packed_dimension}
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
  // §6.11.3 Table 6-8: Apply default signedness per type.
  dtype.is_signed = IsDefaultSigned(dtype.kind);
  Consume();

  // §6.3.2: Parse charge or drive strength for net types.
  ParseNetStrength(dtype);

  // vectored/scalared qualifiers (§6.6.9) — net types only
  dtype.is_vectored = dtype.is_net && Match(TokenKind::kKwVectored);
  if (dtype.is_net && !dtype.is_vectored) {
    dtype.is_scalared = Match(TokenKind::kKwScalared);
  }

  // §6.7.1: data_type_or_implicit — check for explicit type after net keyword.
  bool has_intervening = dtype.drive_strength0 != 0 ||
                         dtype.charge_strength != 0 || dtype.is_vectored ||
                         dtype.is_scalared;
  if (dtype.is_net && TryParseNetDataType(dtype, has_intervening)) return dtype;

  // §6.11.3: Explicit signed/unsigned overrides the default.
  if (Match(TokenKind::kKwSigned)) {
    dtype.is_signed = true;
  } else if (Match(TokenKind::kKwUnsigned)) {
    dtype.is_signed = false;
  }

  ParsePackedDims(dtype);
  return dtype;
}

// --- Unpacked dimensions ---

// Check if current token is a type keyword for associative array index (§7.8).
static bool IsAssocIndexType(TokenKind tk) {
  return TokenToTypeKind(tk).has_value() && tk != TokenKind::kKwVoid;
}

void Parser::ParseUnpackedDims(std::vector<Expr*>& dims) {
  while (Check(TokenKind::kLBracket)) {
    Consume();
    if (Match(TokenKind::kRBracket)) {
      dims.push_back(nullptr);  // dynamic array []
      continue;
    }
    if (Match(TokenKind::kDollar)) {
      // Queue: [$] or [$:N]
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
      // Associative: [*]
      auto* dim = arena_.Create<Expr>();
      dim->kind = ExprKind::kIdentifier;
      dim->text = "*";
      dims.push_back(dim);
      Expect(TokenKind::kRBracket);
      continue;
    }
    // Associative array with type index: [string], [int], [byte], etc. (§7.8)
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

// --- Variable declaration list ---

void Parser::ParseVarDeclList(std::vector<ModuleItem*>& items,
                              const DataType& dtype) {
  Expr* nd1 = nullptr;
  Expr* nd2 = nullptr;
  Expr* nd3 = nullptr;
  if (dtype.is_net) ParseGateDelay(nd1, nd2, nd3);
  do {
    auto* item = arena_.Create<ModuleItem>();
    item->kind =
        dtype.is_net ? ModuleItemKind::kNetDecl : ModuleItemKind::kVarDecl;
    item->loc = CurrentLoc();
    item->data_type = dtype;
    item->drive_strength0 = dtype.drive_strength0;
    item->drive_strength1 = dtype.drive_strength1;
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

// --- Parameter declarations ---

// type_parameter_declaration: type [forward_type] list_of_type_assignments
void Parser::ParseTypeParamDecl(std::vector<ModuleItem*>& items,
                                SourceLoc loc, bool localparam) {
  // Optional forward_type: enum | struct | union | class | interface class
  DataTypeKind fwd = DataTypeKind::kImplicit;
  if (Check(TokenKind::kKwEnum) || Check(TokenKind::kKwStruct) ||
      Check(TokenKind::kKwUnion) || Check(TokenKind::kKwClass) ||
      Check(TokenKind::kKwInterface)) {
    if (Match(TokenKind::kKwInterface)) {
      Expect(TokenKind::kKwClass);
      fwd = DataTypeKind::kVoid;  // Reuse kVoid for interface class.
    } else {
      if (Check(TokenKind::kKwEnum)) fwd = DataTypeKind::kEnum;
      else if (Check(TokenKind::kKwStruct)) fwd = DataTypeKind::kStruct;
      else if (Check(TokenKind::kKwUnion)) fwd = DataTypeKind::kUnion;
      else if (Check(TokenKind::kKwClass)) fwd = DataTypeKind::kNamed;
      Consume();
    }
  }
  // list_of_type_assignments: type_assignment { , type_assignment }
  do {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kParamDecl;
    item->is_localparam = localparam;
    item->loc = loc;
    item->data_type.kind = DataTypeKind::kVoid;  // Marker for type params.
    item->forward_type_kind = fwd;
    item->name = Expect(TokenKind::kIdentifier).text;
    if (Match(TokenKind::kEq)) {
      auto dtype = ParseDataType();
      if (dtype.kind != DataTypeKind::kImplicit) {
        item->typedef_type = dtype;
      } else {
        item->init_expr = ParseExpr();
      }
    }
    known_types_.insert(item->name);
    items.push_back(item);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
}

void Parser::ParseParamDecl(std::vector<ModuleItem*>& items) {
  auto loc = CurrentLoc();
  bool localparam = Check(TokenKind::kKwLocalparam);
  Consume();  // parameter or localparam
  // type_parameter_declaration: type [forward_type] list_of_type_assignments
  if (Match(TokenKind::kKwType)) {
    ParseTypeParamDecl(items, loc, localparam);
    return;
  }
  DataType dtype = ParseDataType();
  // Handle implicit type with packed dims: localparam [10:0] p (§6.10)
  if (dtype.kind == DataTypeKind::kImplicit && Check(TokenKind::kLBracket)) {
    dtype.kind = DataTypeKind::kLogic;
    Consume();
    dtype.packed_dim_left = ParseExpr();
    Expect(TokenKind::kColon);
    dtype.packed_dim_right = ParseExpr();
    Expect(TokenKind::kRBracket);
  }
  // list_of_param_assignments: param_assignment { , param_assignment }
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
    }
    items.push_back(item);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
}

// §6.23 / A.2.2.1: type_reference used as data_type in declaration.
bool Parser::TryParseTypeRef(std::vector<ModuleItem*>& items) {
  if (!Check(TokenKind::kKwType)) return false;
  Consume();  // type
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
