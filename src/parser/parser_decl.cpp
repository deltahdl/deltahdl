#include <optional>

#include "parser/parser.h"

namespace delta {

// --- Defparam parsing ---

ModuleItem* Parser::ParseDefparam() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kDefparam;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwDefparam);

  do {
    Expr* path = ParseExpr();
    Expect(TokenKind::kEq);
    Expr* value = ParseExpr();
    item->defparam_assigns.emplace_back(path, value);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
  return item;
}

// --- Enum type parsing ---

DataType Parser::ParseEnumType() {
  DataType dtype;
  dtype.kind = DataTypeKind::kEnum;
  Expect(TokenKind::kKwEnum);

  // Optional base type (e.g. enum logic [7:0] { ... }).
  auto base = ParseDataType();
  if (base.kind != DataTypeKind::kImplicit) {
    dtype.is_signed = base.is_signed;
    dtype.packed_dim_left = base.packed_dim_left;
    dtype.packed_dim_right = base.packed_dim_right;
  }

  dtype = ParseEnumBody(dtype);

  return dtype;
}

// --- Enum body with range syntax (§6.19.2) ---

DataType Parser::ParseEnumBody(const DataType& base) {
  DataType dtype = base;
  Expect(TokenKind::kLBrace);
  do {
    EnumMember member;
    member.name = Expect(TokenKind::kIdentifier).text;
    // Optional range: name[N] or name[N:M] (§6.19.2)
    if (Match(TokenKind::kLBracket)) {
      member.range_start = ParseExpr();
      if (Match(TokenKind::kColon)) {
        member.range_end = ParseExpr();
      }
      Expect(TokenKind::kRBracket);
    }
    if (Match(TokenKind::kEq)) {
      member.value = ParseExpr();
    }
    dtype.enum_members.push_back(member);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kRBrace);
  return dtype;
}

// --- Struct/union type parsing ---

DataType Parser::ParseStructOrUnionType() {
  DataType dtype;
  dtype.kind = Check(TokenKind::kKwStruct) ? DataTypeKind::kStruct
                                           : DataTypeKind::kUnion;
  Consume();  // struct or union

  // Union qualifiers: tagged, soft (§7.3)
  if (dtype.kind == DataTypeKind::kUnion) {
    if (Match(TokenKind::kKwTagged)) dtype.is_tagged = true;
    if (Match(TokenKind::kKwSoft)) dtype.is_soft = true;
  }

  if (Match(TokenKind::kKwPacked)) {
    dtype.is_packed = true;
    if (Match(TokenKind::kKwSigned)) {
      dtype.is_signed = true;
    } else {
      Match(TokenKind::kKwUnsigned);
    }
  }

  ParseStructMembers(dtype);
  return dtype;
}

DataType Parser::ParseStructOrUnionBody(TokenKind kw) {
  DataType dtype;
  dtype.kind = (kw == TokenKind::kKwStruct) ? DataTypeKind::kStruct
                                            : DataTypeKind::kUnion;
  ParseStructMembers(dtype);
  return dtype;
}

void Parser::ParseStructMembers(DataType& dtype) {
  Expect(TokenKind::kLBrace);
  while (!Check(TokenKind::kRBrace) && !AtEnd()) {
    auto member_type = ParseDataType();
    do {
      StructMember member;
      member.type_kind = member_type.kind;
      member.is_signed = member_type.is_signed;
      member.packed_dim_left = member_type.packed_dim_left;
      member.packed_dim_right = member_type.packed_dim_right;
      member.name = Expect(TokenKind::kIdentifier).text;
      ParseUnpackedDims(member.unpacked_dims);
      if (Match(TokenKind::kEq)) {
        member.init_expr = ParseExpr();
      }
      dtype.struct_members.push_back(member);
    } while (Match(TokenKind::kComma));
    Expect(TokenKind::kSemicolon);
  }
  Expect(TokenKind::kRBrace);
}

// --- Typedef parsing ---

ModuleItem* Parser::ParseTypedef() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kTypedef;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwTypedef);

  if (Check(TokenKind::kKwEnum)) {
    item->typedef_type = ParseEnumType();
  } else if (Check(TokenKind::kKwStruct) || Check(TokenKind::kKwUnion)) {
    item->typedef_type = ParseStructOrUnionType();
  } else {
    item->typedef_type = ParseDataType();
  }

  item->name = Expect(TokenKind::kIdentifier).text;
  ParseUnpackedDims(item->unpacked_dims);
  known_types_.insert(item->name);
  Expect(TokenKind::kSemicolon);
  return item;
}

// --- Nettype declaration (§6.6.7 stub) ---

ModuleItem* Parser::ParseNettypeDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kTypedef;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwNettype);
  item->typedef_type = ParseDataType();
  item->name = Expect(TokenKind::kIdentifier).text;
  // Optional "with resolve_fn" clause — consume but ignore.
  if (Check(TokenKind::kKwWith)) {
    Consume();
    Consume();  // resolution function identifier
  }
  known_types_.insert(item->name);
  Expect(TokenKind::kSemicolon);
  return item;
}

// --- Function argument list ---

std::vector<FunctionArg> Parser::ParseFunctionArgs() {
  std::vector<FunctionArg> args;
  Expect(TokenKind::kLParen);
  if (Check(TokenKind::kRParen)) {
    Consume();
    return args;
  }
  Direction sticky_dir = Direction::kNone;
  do {
    FunctionArg arg;
    // const ref (§13.5.2)
    if (Match(TokenKind::kKwConst)) {
      arg.is_const = true;
    }
    if (Check(TokenKind::kKwInput)) {
      arg.direction = Direction::kInput;
      sticky_dir = Direction::kInput;
      Consume();
    } else if (Check(TokenKind::kKwOutput)) {
      arg.direction = Direction::kOutput;
      sticky_dir = Direction::kOutput;
      Consume();
    } else if (Check(TokenKind::kKwInout)) {
      arg.direction = Direction::kInout;
      sticky_dir = Direction::kInout;
      Consume();
    } else if (Check(TokenKind::kKwRef)) {
      arg.direction = Direction::kRef;
      sticky_dir = Direction::kRef;
      Consume();
    } else {
      arg.direction = sticky_dir;
    }
    arg.data_type = ParseDataType();
    arg.name = Expect(TokenKind::kIdentifier).text;
    // Unpacked dimensions on argument (§13.4)
    ParseUnpackedDims(arg.unpacked_dims);
    // Default value (§13.5.3)
    if (Match(TokenKind::kEq)) {
      arg.default_value = ParseExpr();
    }
    args.push_back(arg);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kRParen);
  return args;
}

// --- Function declaration ---

ModuleItem* Parser::ParseFunctionDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kFunctionDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwFunction);

  // Optional lifetime: automatic or static.
  if (Match(TokenKind::kKwAutomatic)) {
    item->is_automatic = true;
  } else if (Match(TokenKind::kKwStatic)) {
    item->is_static = true;
  }

  // Return type (may be void or a data type).
  if (Check(TokenKind::kKwVoid)) {
    item->return_type.kind = DataTypeKind::kVoid;
    Consume();
  } else if (Check(TokenKind::kLBracket)) {
    // Implicit type with packed dims: function [7:0] name;
    Consume();
    item->return_type.packed_dim_left = ParseExpr();
    Expect(TokenKind::kColon);
    item->return_type.packed_dim_right = ParseExpr();
    Expect(TokenKind::kRBracket);
  } else {
    item->return_type = ParseDataType();
  }

  item->name = Expect(TokenKind::kIdentifier).text;

  if (Check(TokenKind::kLParen)) {
    item->func_args = ParseFunctionArgs();
  }
  Expect(TokenKind::kSemicolon);

  // Old-style port declarations (§13.3)
  ParseOldStylePortDecls(item, TokenKind::kKwEndfunction);

  while (!Check(TokenKind::kKwEndfunction) && !AtEnd()) {
    item->func_body_stmts.push_back(ParseStmt());
  }
  Expect(TokenKind::kKwEndfunction);
  // Optional end label: ": name"
  if (Match(TokenKind::kColon)) {
    ExpectIdentifier();
  }
  return item;
}

// --- Task declaration ---

ModuleItem* Parser::ParseTaskDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kTaskDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwTask);

  if (Match(TokenKind::kKwAutomatic)) {
    item->is_automatic = true;
  } else if (Match(TokenKind::kKwStatic)) {
    item->is_static = true;
  }

  item->name = Expect(TokenKind::kIdentifier).text;

  if (Check(TokenKind::kLParen)) {
    item->func_args = ParseFunctionArgs();
  }
  Expect(TokenKind::kSemicolon);

  // Old-style port declarations (§13.3)
  ParseOldStylePortDecls(item, TokenKind::kKwEndtask);

  while (!Check(TokenKind::kKwEndtask) && !AtEnd()) {
    item->func_body_stmts.push_back(ParseStmt());
  }
  Expect(TokenKind::kKwEndtask);
  // Optional end label: ": name"
  if (Match(TokenKind::kColon)) {
    ExpectIdentifier();
  }
  return item;
}

// --- Event lists ---

std::vector<EventExpr> Parser::ParseEventList() {
  std::vector<EventExpr> events;
  events.push_back(ParseSingleEvent());
  while (Match(TokenKind::kKwOr) || Match(TokenKind::kComma)) {
    events.push_back(ParseSingleEvent());
  }
  return events;
}

EventExpr Parser::ParseSingleEvent() {
  EventExpr ev;
  if (Match(TokenKind::kKwPosedge)) {
    ev.edge = Edge::kPosedge;
  } else if (Match(TokenKind::kKwNegedge)) {
    ev.edge = Edge::kNegedge;
  }
  ev.signal = ParseExpr();
  // iff guard (§9.4.2)
  if (Match(TokenKind::kKwIff)) {
    ev.iff_condition = ParseExpr();
  }
  return ev;
}

// --- Old-style port declarations (§13.3) ---

void Parser::ParseOldStylePortDecls(ModuleItem* item, TokenKind end_kw) {
  // Parse port direction declarations before the function/task body.
  while (Check(TokenKind::kKwInput) || Check(TokenKind::kKwOutput) ||
         Check(TokenKind::kKwInout) || Check(TokenKind::kKwRef)) {
    FunctionArg arg;
    if (Check(TokenKind::kKwInput)) {
      arg.direction = Direction::kInput;
    } else if (Check(TokenKind::kKwOutput)) {
      arg.direction = Direction::kOutput;
    } else if (Check(TokenKind::kKwInout)) {
      arg.direction = Direction::kInout;
    } else {
      arg.direction = Direction::kRef;
    }
    Consume();
    arg.data_type = ParseDataType();
    arg.name = Expect(TokenKind::kIdentifier).text;
    Expect(TokenKind::kSemicolon);
    item->func_args.push_back(arg);
  }
  (void)end_kw;
}

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

// clang-format off
static std::optional<DataTypeKind> TokenToTypeKind(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwLogic:    return DataTypeKind::kLogic;
    case TokenKind::kKwReg:      return DataTypeKind::kReg;
    case TokenKind::kKwBit:      return DataTypeKind::kBit;
    case TokenKind::kKwByte:     return DataTypeKind::kByte;
    case TokenKind::kKwShortint: return DataTypeKind::kShortint;
    case TokenKind::kKwInt:      return DataTypeKind::kInt;
    case TokenKind::kKwLongint:  return DataTypeKind::kLongint;
    case TokenKind::kKwInteger:  return DataTypeKind::kInteger;
    case TokenKind::kKwReal:     return DataTypeKind::kReal;
    case TokenKind::kKwShortreal:return DataTypeKind::kShortreal;
    case TokenKind::kKwRealtime: return DataTypeKind::kRealtime;
    case TokenKind::kKwTime:     return DataTypeKind::kTime;
    case TokenKind::kKwString:   return DataTypeKind::kString;
    case TokenKind::kKwEvent:    return DataTypeKind::kEvent;
    case TokenKind::kKwVoid:     return DataTypeKind::kVoid;
    case TokenKind::kKwChandle:  return DataTypeKind::kChandle;
    case TokenKind::kKwWire:     return DataTypeKind::kWire;
    case TokenKind::kKwTri:      return DataTypeKind::kTri;
    case TokenKind::kKwTriand:   return DataTypeKind::kTriand;
    case TokenKind::kKwTrior:    return DataTypeKind::kTrior;
    case TokenKind::kKwTri0:     return DataTypeKind::kTri0;
    case TokenKind::kKwTri1:     return DataTypeKind::kTri1;
    case TokenKind::kKwTrireg:   return DataTypeKind::kTrireg;
    case TokenKind::kKwWand:     return DataTypeKind::kWand;
    case TokenKind::kKwWor:      return DataTypeKind::kWor;
    case TokenKind::kKwSupply0:  return DataTypeKind::kSupply0;
    case TokenKind::kKwSupply1:  return DataTypeKind::kSupply1;
    case TokenKind::kKwUwire:    return DataTypeKind::kUwire;
    default:                     return std::nullopt;
  }
}
// clang-format on

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

DataType Parser::ParseDataType() {
  DataType dtype;

  if (Match(TokenKind::kKwConst)) {
    dtype.is_const = true;
  }

  // Virtual interface type: virtual [interface] type_name [.modport] (§25.9)
  if (Check(TokenKind::kKwVirtual)) {
    Consume();
    dtype.kind = DataTypeKind::kVirtualInterface;
    Match(TokenKind::kKwInterface);  // optional 'interface' keyword
    dtype.type_name = Expect(TokenKind::kIdentifier).text;
    if (Match(TokenKind::kDot)) {
      dtype.modport_name = Expect(TokenKind::kIdentifier).text;
    }
    return dtype;
  }

  if (CurrentToken().Is(TokenKind::kIdentifier) &&
      known_types_.count(CurrentToken().text) != 0) {
    dtype.kind = DataTypeKind::kNamed;
    dtype.type_name = Consume().text;
    return dtype;
  }

  auto tok_kind = CurrentToken().kind;
  auto kind = TokenToTypeKind(tok_kind);
  if (!kind) return dtype;
  dtype.kind = *kind;
  dtype.is_net = IsNetTypeToken(tok_kind);
  Consume();

  // §6.6.4: charge_strength for trireg — (small), (medium), (large)
  if (dtype.kind == DataTypeKind::kTrireg) {
    dtype.charge_strength = ParseChargeStrength();
  }

  // vectored/scalared qualifiers (§6.6.9) — net types only
  if (dtype.is_net) {
    if (Match(TokenKind::kKwVectored)) {
      dtype.is_vectored = true;
    } else if (Match(TokenKind::kKwScalared)) {
      dtype.is_scalared = true;
    }
  }

  if (Match(TokenKind::kKwSigned)) {
    dtype.is_signed = true;
  } else if (Match(TokenKind::kKwUnsigned)) {
    dtype.is_signed = false;
  }

  if (Check(TokenKind::kLBracket)) {
    Consume();
    dtype.packed_dim_left = ParseExpr();
    Expect(TokenKind::kColon);
    dtype.packed_dim_right = ParseExpr();
    Expect(TokenKind::kRBracket);
  }
  return dtype;
}

// --- Unpacked dimensions ---

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

void Parser::ParseNetDelay(Expr*& d1, Expr*& d2, Expr*& d3) {
  if (!Check(TokenKind::kHash)) return;
  Consume();  // '#'
  if (Match(TokenKind::kLParen)) {
    d1 = ParseExpr();
    if (Match(TokenKind::kComma)) {
      d2 = ParseExpr();
      if (Match(TokenKind::kComma)) d3 = ParseExpr();
    }
    Expect(TokenKind::kRParen);
  } else {
    d1 = ParsePrimaryExpr();
  }
}

void Parser::ParseVarDeclList(std::vector<ModuleItem*>& items,
                              const DataType& dtype) {
  Expr* nd1 = nullptr;
  Expr* nd2 = nullptr;
  Expr* nd3 = nullptr;
  if (dtype.is_net) ParseNetDelay(nd1, nd2, nd3);
  do {
    auto* item = arena_.Create<ModuleItem>();
    item->kind =
        dtype.is_net ? ModuleItemKind::kNetDecl : ModuleItemKind::kVarDecl;
    item->loc = CurrentLoc();
    item->data_type = dtype;
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

ModuleItem* Parser::ParseParamDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kParamDecl;
  item->loc = CurrentLoc();
  Consume();  // parameter or localparam
  // Handle "parameter type T = ..." (type parameter, §6.20.3).
  if (Match(TokenKind::kKwType)) {
    item->data_type.kind = DataTypeKind::kVoid;  // Marker for type params.
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
    Expect(TokenKind::kSemicolon);
    return item;
  } else {
    item->data_type = ParseDataType();
    // Handle implicit type with packed dims: localparam [10:0] p (§6.10)
    if (item->data_type.kind == DataTypeKind::kImplicit &&
        Check(TokenKind::kLBracket)) {
      item->data_type.kind = DataTypeKind::kLogic;
      Consume();
      item->data_type.packed_dim_left = ParseExpr();
      Expect(TokenKind::kColon);
      item->data_type.packed_dim_right = ParseExpr();
      Expect(TokenKind::kRBracket);
    }
  }
  auto name_tok = Expect(TokenKind::kIdentifier);
  item->name = name_tok.text;
  ParseUnpackedDims(item->unpacked_dims);
  if (Match(TokenKind::kEq)) {
    item->init_expr = ParseExpr();
  }
  Expect(TokenKind::kSemicolon);
  return item;
}

}  // namespace delta
