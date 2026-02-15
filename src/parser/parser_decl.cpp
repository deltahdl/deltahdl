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
    // A.2.2.1: {attribute_instance} [random_qualifier] data_type_or_void ...
    auto member_attrs = ParseAttributes();
    bool is_rand = Match(TokenKind::kKwRand);
    bool is_randc = !is_rand && Match(TokenKind::kKwRandc);

    DataType member_type;
    if (Check(TokenKind::kKwStruct) || Check(TokenKind::kKwUnion)) {
      member_type = ParseStructOrUnionType();
    } else {
      member_type = ParseDataType();
    }
    if (member_type.kind == DataTypeKind::kImplicit && !CheckIdentifier()) {
      Synchronize();
      continue;
    }
    do {
      StructMember member;
      member.type_kind = member_type.kind;
      member.is_signed = member_type.is_signed;
      member.is_rand = is_rand;
      member.is_randc = is_randc;
      member.attrs = member_attrs;
      member.packed_dim_left = member_type.packed_dim_left;
      member.packed_dim_right = member_type.packed_dim_right;
      member.extra_packed_dims = member_type.extra_packed_dims;
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

  // A.2.1.3 forward_type: typedef [enum|struct|union|class|interface class] id
  // ;
  if (Check(TokenKind::kKwClass) || Check(TokenKind::kKwInterface)) {
    Consume();
    if (Check(TokenKind::kKwClass)) Consume();  // "interface class"
    item->name = Expect(TokenKind::kIdentifier).text;
    known_types_.insert(item->name);
    Expect(TokenKind::kSemicolon);
    return item;
  }
  // Forward typedef for enum/struct/union: typedef enum|struct|union IDENT ;
  if (Check(TokenKind::kKwEnum) || Check(TokenKind::kKwStruct) ||
      Check(TokenKind::kKwUnion)) {
    auto saved = lexer_.SavePos();
    Consume();  // enum/struct/union
    if (CheckIdentifier()) {
      auto id_saved = lexer_.SavePos();
      auto id_tok = Consume();
      if (Check(TokenKind::kSemicolon)) {
        // Forward declaration: typedef enum/struct/union IDENT ;
        item->name = id_tok.text;
        known_types_.insert(item->name);
        Expect(TokenKind::kSemicolon);
        return item;
      }
      lexer_.RestorePos(id_saved);
    }
    lexer_.RestorePos(saved);
  }
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
  item->kind = ModuleItemKind::kNettypeDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwNettype);
  item->typedef_type = ParseDataType();
  item->name = Expect(TokenKind::kIdentifier).text;
  // A.2.1.3: with [ package_scope | class_scope ] tf_identifier
  if (Check(TokenKind::kKwWith)) {
    Consume();
    auto func_name = Expect(TokenKind::kIdentifier).text;
    if (Match(TokenKind::kColonColon)) {
      // Scoped: pkg::func or class::func — store the function name
      item->nettype_resolve_func = Expect(TokenKind::kIdentifier).text;
    } else {
      item->nettype_resolve_func = func_name;
    }
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

// --- Function return type ---

DataType Parser::ParseFunctionReturnType() {
  if (Check(TokenKind::kKwVoid)) {
    DataType dt;
    dt.kind = DataTypeKind::kVoid;
    Consume();
    return dt;
  }
  if (Check(TokenKind::kLBracket)) {
    DataType dt;
    Consume();
    dt.packed_dim_left = ParseExpr();
    Expect(TokenKind::kColon);
    dt.packed_dim_right = ParseExpr();
    Expect(TokenKind::kRBracket);
    return dt;
  }
  return ParseDataType();
}

// --- Function declaration ---

ModuleItem* Parser::ParseFunctionDecl(bool prototype_only) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kFunctionDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwFunction);

  // Optional lifetime: automatic or static.
  item->is_automatic = Match(TokenKind::kKwAutomatic);
  if (!item->is_automatic) item->is_static = Match(TokenKind::kKwStatic);

  item->return_type = ParseFunctionReturnType();

  // §8.7 constructors use 'new' as function name
  item->name =
      Match(TokenKind::kKwNew) ? "new" : Expect(TokenKind::kIdentifier).text;
  // §8.24 out-of-block methods: class_name::method_name
  // class_constructor_declaration: function class_scope new (A.1.11)
  while (Match(TokenKind::kColonColon)) {
    item->name =
        Match(TokenKind::kKwNew) ? "new" : Expect(TokenKind::kIdentifier).text;
  }

  if (Check(TokenKind::kLParen)) {
    item->func_args = ParseFunctionArgs();
  }
  Expect(TokenKind::kSemicolon);

  // Pure virtual / extern prototypes have no body (§8.21, §8.24)
  if (prototype_only) return item;

  // Old-style port declarations (§13.3)
  ParseOldStylePortDecls(item, TokenKind::kKwEndfunction);

  while (!Check(TokenKind::kKwEndfunction) && !AtEnd()) {
    if (IsBlockVarDeclStart()) {
      ParseBlockVarDecls(item->func_body_stmts);
    } else {
      item->func_body_stmts.push_back(ParseStmt());
    }
  }
  Expect(TokenKind::kKwEndfunction);
  // Optional end label: ": name" (may be 'new' for constructors)
  if (Match(TokenKind::kColon)) {
    if (!Match(TokenKind::kKwNew)) ExpectIdentifier();
  }
  return item;
}

// --- Task declaration ---

ModuleItem* Parser::ParseTaskDecl(bool prototype_only) {
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
  // §8.24 out-of-block methods: class_name::method_name
  while (Match(TokenKind::kColonColon)) {
    item->name = Expect(TokenKind::kIdentifier).text;
  }

  if (Check(TokenKind::kLParen)) {
    item->func_args = ParseFunctionArgs();
  }
  Expect(TokenKind::kSemicolon);

  // Pure virtual / extern prototypes have no body (§8.21, §8.24)
  if (prototype_only) return item;

  // Old-style port declarations (§13.3)
  ParseOldStylePortDecls(item, TokenKind::kKwEndtask);

  while (!Check(TokenKind::kKwEndtask) && !AtEnd()) {
    if (IsBlockVarDeclStart()) {
      ParseBlockVarDecls(item->func_body_stmts);
    } else {
      item->func_body_stmts.push_back(ParseStmt());
    }
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
  } else if (Match(TokenKind::kKwEdge)) {
    ev.edge = Edge::kEdge;
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

// Virtual interface type: virtual [interface] type_name [.modport] (§25.9)
DataType Parser::ParseVirtualInterfaceType() {
  DataType dtype;
  dtype.kind = DataTypeKind::kVirtualInterface;
  Match(TokenKind::kKwInterface);
  dtype.type_name = Expect(TokenKind::kIdentifier).text;
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
  while (Match(TokenKind::kColonColon)) {
    dtype.scope_name = dtype.type_name;
    dtype.type_name = ExpectIdentifier().text;
    if (Check(TokenKind::kHash)) {
      Consume();
      dtype.type_params = ParseTypeParamList();
    }
  }
  return dtype;
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
    return named;
  }

  // A.2.2.1: implicit_data_type ::= [signing] {packed_dimension}
  // Handle bare signed/unsigned before packed dimensions.
  if (Check(TokenKind::kKwSigned) || Check(TokenKind::kKwUnsigned)) {
    dtype.is_signed = Match(TokenKind::kKwSigned);
    if (!dtype.is_signed) Consume();  // unsigned
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
                                SourceLoc loc) {
  // Optional forward_type: enum | struct | union | class | interface class
  if (Check(TokenKind::kKwEnum) || Check(TokenKind::kKwStruct) ||
      Check(TokenKind::kKwUnion) || Check(TokenKind::kKwClass) ||
      Check(TokenKind::kKwInterface)) {
    if (Match(TokenKind::kKwInterface)) {
      Expect(TokenKind::kKwClass);
    } else {
      Consume();
    }
  }
  // list_of_type_assignments: type_assignment { , type_assignment }
  do {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kParamDecl;
    item->loc = loc;
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
    items.push_back(item);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
}

void Parser::ParseParamDecl(std::vector<ModuleItem*>& items) {
  auto loc = CurrentLoc();
  Consume();  // parameter or localparam
  // type_parameter_declaration: type [forward_type] list_of_type_assignments
  if (Match(TokenKind::kKwType)) {
    ParseTypeParamDecl(items, loc);
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

}  // namespace delta
