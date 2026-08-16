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

// A.2.2.1: the integer vector types are the ones written with a packed part;
// every other data type either fixes its own width or has none to leave
// unspecified, so only these can carry a packed dimension with no range.
static bool TakesPackedPart(DataTypeKind kind) {
  return kind == DataTypeKind::kBit || kind == DataTypeKind::kLogic ||
         kind == DataTypeKind::kReg;
}

// §H.2: true when the parser stands at an empty bracket pair "[]" that `dtype`
// may carry as a packed dimension whose range is left unspecified. The form is
// admitted only where the standard grants it -- the formal arguments of a DPI
// import declaration -- so elsewhere an empty pair is left for whoever parses
// the unpacked dimensions that follow the declared name.
bool Parser::AtUnsizedPackedDim(const DataType& dtype) {
  if (!in_dpi_import_formals_ || !TakesPackedPart(dtype.kind)) return false;
  if (!Check(TokenKind::kLBracket)) return false;
  auto saved = lexer_.SavePos();
  Consume();
  bool is_empty = Check(TokenKind::kRBracket);
  lexer_.RestorePos(saved);
  return is_empty;
}

// §H.2: consume the empty bracket pair the caller has already confirmed and
// record it as this type's unsized packed dimension. There are no bounds to
// keep, so the flag is the whole of what the pair contributes.
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
    // §7.4.1 states the rule both these calls enforce: "Each packed dimension
    // in a packed array declaration shall be specified by a range
    // specification of the form [ constant_expression : constant_expression
    // ]", and its NOTE rules out the single-number form "[8]" by name. "Each
    // packed dimension" covers the first as squarely as the fifth, so the
    // first names the clause the loop below already names rather than a second
    // one. §6.9 has no rule to cite here. It defines a scalar and a vector and
    // defers the form to §7.4, and this function parses the packed dimensions
    // of a struct, union, enum, named type and port type, none of which is a
    // vector.
    Expect(TokenKind::kColon, Subclause("7.4.1"));
    dtype.packed_dim_right = ParseExpr();
    Expect(TokenKind::kRBracket, Subclause("7.4.1"));
  }

  while (Check(TokenKind::kLBracket)) {
    if (AtUnsizedPackedDim(dtype)) {
      // A second empty pair belongs to the unpacked part, which is written
      // after the declared name and parsed there. Only the first one can be
      // this type's packed dimension, so stop rather than claim it.
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

// Parses one element of a parameter_value_assignment list. An ordered element
// is a bare data type or expression; a named element is ".name(value)", whose
// formal name is recorded on the value's DataType (§6.20 / Syntax 8-2).
DataType Parser::ParseOneTypeParam() {
  if (Match(TokenKind::kDot)) {
    std::string_view arg_name =
        Expect(TokenKind::kIdentifier, Subclause("23.10.2.2")).text;
    Expect(TokenKind::kLParen, Subclause("23.10.2.2"));
    DataType dt;
    if (!Check(TokenKind::kRParen)) {
      dt = ParseDataType();
      if (dt.kind == DataTypeKind::kImplicit) dt.type_ref_expr = ParseExpr();
    }
    Expect(TokenKind::kRParen, Subclause("23.10.2.2"));
    dt.param_arg_name = arg_name;
    return dt;
  }
  DataType dt = ParseDataType();
  if (dt.kind == DataTypeKind::kImplicit) dt.type_ref_expr = ParseExpr();
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
    // §A.2.1.3 writes the two strengths as alternatives, `net_type
    // [ drive_strength | charge_strength ]`, so a charge strength is the whole
    // of the strength specification and nothing further belongs to it. Reading
    // none is not the end of the specification, because §A.2.2.1 lists trireg
    // among the net types and §6.3.2 restricts a drive strength only to a
    // declaration that places a continuous assignment on the net. So fall
    // through to the drive strength parse below, which ParseChargeStrength
    // left the position for by restoring it.
    if (dtype.charge_strength != 0) return;
  } else {
    if (!dtype.is_net || !Check(TokenKind::kLParen)) return;
    // §6.3.2.1: the charge strength specification shall be used only with
    // trireg nets. Read the specification here and report the rule it breaks,
    // so the declarator list parses on and the report names the rule rather
    // than the identifier the list did not find. The strength is not recorded
    // on the type, because a net that may not carry one has none.
    SourceLoc charge_loc = CurrentLoc();
    if (ParseChargeStrength() != 0) {
      diag_.Error(charge_loc,
                  "charge strength can only be used with trireg nets",
                  Subclause("6.3.2.1"));
      return;
    }
  }
  // Both paths above reach here with the position on whatever token they
  // declined to read as a charge strength, which is a parenthesis on the
  // non-trireg path and anything at all on the trireg one.
  if (!Check(TokenKind::kLParen)) return;
  auto saved = lexer_.SavePos();
  Consume();
  if (IsStrengthToken(CurrentToken().kind)) {
    ParseDriveStrength(dtype.drive_strength0, dtype.drive_strength1);
    Expect(TokenKind::kRParen, Subclause("6.3.2.2"));
  } else {
    lexer_.RestorePos(saved);
  }
}

DataType Parser::ParseNamedType() {
  DataType dtype;
  dtype.kind = DataTypeKind::kNamed;
  dtype.type_name = Consume().text;

  // §6.7.2 / A.2.1.3: a user-defined nettype name takes a delay control here
  // (e.g. `mynet #5 x;`), not a parameter value assignment. Leave the `#` for
  // the net-delay parse in ParseVarDeclList; only a non-nettype named type
  // (e.g. a parameterized class `C#(...)`) consumes `#(` as type parameters.
  if (Check(TokenKind::kHash) && known_nettypes_.count(dtype.type_name) == 0) {
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
                "net type keyword shall not be followed directly by 'reg'",
                Subclause("6.7.1"));
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
    Expect(TokenKind::kLParen, Subclause("6.23"));
    dtype.type_ref_expr = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("6.23"));
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
    // §6.3.2: trireg is a charge-storage net whose net-type kind carries
    // distinct semantics, so keep kTrireg over the inner data type. Other nets
    // adopt the inner data type kind so the §6.7.1 4-state check can inspect it
    // (e.g. reject `wire bit` / `wire real`).
    if (dtype.kind != DataTypeKind::kTrireg) dtype.kind = *inner_kind;
    dtype.is_signed = IsDefaultSigned(*inner_kind);
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

  bool is_named = Check(TokenKind::kIdentifier) &&
                  known_types_.count(CurrentToken().text) != 0;
  if (is_named) {
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
  dtype.type_name = CurrentToken().text;
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

// A.2.2.1 attaches an optional signing to the integer types alone:
// `integer_vector_type [ signing ] { packed_dimension }` and
// `integer_atom_type [ signing ]`. No other data_type production admits one.
static bool TakesSigning(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwBit:
    case TokenKind::kKwLogic:
    case TokenKind::kKwReg:
    case TokenKind::kKwByte:
    case TokenKind::kKwShortint:
    case TokenKind::kKwInt:
    case TokenKind::kKwLongint:
    case TokenKind::kKwInteger:
    case TokenKind::kKwTime:
      return true;
    default:
      return false;
  }
}

// Parses the type naming an associative array's index, positioned on the type
// keyword. §7.8 makes an index_type a data_type, so a data_type built on an
// integer type carries the optional signing that A.2.2.1 gives it and
// `[byte unsigned]` is a legal index type. The qualifier is held in `op`
// because it decides how the keys order: an unsigned byte index sorts key 200
// above key 50, while a signed one reads that key as -56 and sorts it below.
Expr* Parser::ParseAssocIndexDim() {
  auto* dim = arena_.Create<Expr>();
  dim->kind = ExprKind::kIdentifier;
  bool takes_signing = TakesSigning(CurrentToken().kind);
  // §7.8 writes the index type as the keyword itself, so the dimension begins
  // at that keyword.
  Token type_tok = Consume();
  dim->range.start = type_tok.loc;
  dim->text = type_tok.text;
  if (takes_signing &&
      (Check(TokenKind::kKwSigned) || Check(TokenKind::kKwUnsigned))) {
    dim->op = Consume().kind;
  }
  return dim;
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
      // §7.10 writes the queue dimension as the `$` itself.
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
      // §7.8.1 writes the wildcard index dimension as the `*` itself.
      dim->range.start = star_loc;
      dim->text = "*";
      dims.push_back(dim);
      Expect(TokenKind::kRBracket, Subclause("7.8.1"));
      continue;
    }

    if (IsAssocIndexType(CurrentToken().kind)) {
      dims.push_back(ParseAssocIndexDim());
      Expect(TokenKind::kRBracket, Subclause("7.8"));
      continue;
    }
    auto* expr = ParseExpr();
    if (Match(TokenKind::kColon)) {
      auto* range = arena_.Create<Expr>();
      range->kind = ExprKind::kBinary;
      range->op = TokenKind::kColon;
      // §7.4.2 writes the dimension as its first bound followed by the colon,
      // so it begins where that bound begins.
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
  // §6.7 states the net declaration and §6.8 the variable declaration, and this
  // list is one or the other according to the type that heads it.
  Subclause subclause(actual_dtype.is_net ? "6.7" : "6.8");
  if (actual_dtype.is_net || nettype_named) {
    ParseGateDelay(nd1, nd2, nd3);
    // §10.3.4 puts the drive strength before the delay on a net declaration as
    // well as on an `assign`, so a strength standing here breaks the same rule.
    // Parser::ParseNetStrength read the legal position, back in ParseDataType.
    ReportDriveStrengthAfterDelay(nd1);
  }
  bool first = true;
  do {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = actual_dtype.is_net ? ModuleItemKind::kNetDecl
                                     : ModuleItemKind::kVarDecl;
    item->first_in_decl_list = first;
    first = false;
    item->loc = CurrentLoc();
    item->data_type = actual_dtype;
    item->drive_strength0 = actual_dtype.drive_strength0;
    item->drive_strength1 = actual_dtype.drive_strength1;
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

void Parser::ParseTypeParamDecl(std::vector<ModuleItem*>& items, SourceLoc loc,
                                bool localparam) {
  DataTypeKind fwd = DataTypeKind::kImplicit;
  if (IsForwardTypeParamToken(CurrentToken().kind)) {
    if (Match(TokenKind::kKwInterface)) {
      Expect(TokenKind::kKwClass, Subclause("6.20.3"));
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
    auto name_tok = Expect(TokenKind::kIdentifier, Subclause("6.20.3"));
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
    item->name = Expect(TokenKind::kIdentifier, Subclause("6.20.1")).text;
    ParseUnpackedDims(item->unpacked_dims);
    if (Match(TokenKind::kEq)) {
      item->init_expr = ParseExpr();
    } else {
      // §6.20.1 fn22: omitting the value is legal only in a
      // parameter_port_list (a separate parse path), not here.
      diag_.Error(item->loc, "parameter declaration requires a default value",
                  Subclause("6.20.1"));
    }
    items.push_back(item);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon, Subclause("6.20.1"));
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
  Expect(TokenKind::kColon, Subclause("6.20.2"));
  dtype.packed_dim_right = ParseExpr();
  Expect(TokenKind::kRBracket, Subclause("6.20.2"));
}

bool Parser::TryParseTypeRef(std::vector<ModuleItem*>& items) {
  if (!Check(TokenKind::kKwType)) return false;
  Consume();
  Expect(TokenKind::kLParen, Subclause("6.23"));
  auto* type_expr = ParseExpr();
  Expect(TokenKind::kRParen, Subclause("6.23"));
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kVarDecl;
  item->loc = CurrentLoc();
  item->data_type.type_ref_expr = type_expr;
  item->name = ExpectIdentifier(Subclause("6.8")).text;
  ParseUnpackedDims(item->unpacked_dims);
  Expect(TokenKind::kSemicolon, Subclause("6.8"));
  items.push_back(item);
  return true;
}

}  // namespace delta
