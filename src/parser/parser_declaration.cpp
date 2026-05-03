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
    Expr* value = ParseMinTypMaxExpr();
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
      ParsePackedDims(member_type);
    } else if (Check(TokenKind::kKwEnum)) {
      member_type = ParseEnumType();
      ParsePackedDims(member_type);
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
  // Bare forward typedef: typedef IDENT ;
  if (CheckIdentifier()) {
    auto saved = lexer_.SavePos();
    auto id_tok = Consume();
    if (Check(TokenKind::kSemicolon)) {
      item->name = id_tok.text;
      known_types_.insert(item->name);
      Expect(TokenKind::kSemicolon);
      return item;
    }
    lexer_.RestorePos(saved);
  }
  // A.2.1.3 form 2: typedef ifc_port {[const_expr]} . type_id new_name ;
  if (CheckIdentifier()) {
    auto saved = lexer_.SavePos();
    Consume();  // potential interface port identifier
    // Skip constant_bit_select: { [ constant_expression ] }
    while (Check(TokenKind::kLBracket)) {
      Consume();
      int depth = 1;
      while (depth > 0 && !Check(TokenKind::kEof)) {
        if (CurrentToken().kind == TokenKind::kLBracket) depth++;
        else if (CurrentToken().kind == TokenKind::kRBracket) depth--;
        if (depth > 0) Consume();
      }
      if (Check(TokenKind::kRBracket)) Consume();
    }
    if (Check(TokenKind::kDot)) {
      // Confirmed form 2 — restore and parse properly.
      lexer_.RestorePos(saved);
      item->typedef_ifc_port = Consume().text;
      while (Check(TokenKind::kLBracket)) {
        Consume();
        item->unpacked_dims.push_back(ParseExpr());
        Expect(TokenKind::kRBracket);
      }
      Expect(TokenKind::kDot);
      item->typedef_type.kind = DataTypeKind::kNamed;
      item->typedef_type.type_name = Expect(TokenKind::kIdentifier).text;
      item->name = Expect(TokenKind::kIdentifier).text;
      known_types_.insert(item->name);
      Expect(TokenKind::kSemicolon);
      return item;
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

// A.2.7: Parse port direction and update sticky direction state.
// Returns the resulting sticky direction; sets `was_explicit` to true when a
// direction keyword was actually consumed (per §13.3, the explicit-vs-sticky
// distinction also drives data-type defaulting on the same argument).
Direction Parser::ParseArgDirection(FunctionArg& arg, Direction sticky_dir,
                                    bool* was_explicit) {
  if (was_explicit) *was_explicit = true;
  if (Check(TokenKind::kKwInput)) {
    arg.direction = Direction::kInput;
    Consume();
    return Direction::kInput;
  }
  if (Check(TokenKind::kKwOutput)) {
    arg.direction = Direction::kOutput;
    Consume();
    return Direction::kOutput;
  }
  if (Check(TokenKind::kKwInout)) {
    arg.direction = Direction::kInout;
    Consume();
    return Direction::kInout;
  }
  if (Check(TokenKind::kKwRef)) {
    arg.direction = Direction::kRef;
    Consume();
    arg.is_ref_static = Match(TokenKind::kKwStatic);  // A.2.7: ref [static]
    return Direction::kRef;
  }
  arg.direction = sticky_dir;
  if (was_explicit) *was_explicit = false;
  return sticky_dir;
}

std::vector<FunctionArg> Parser::ParseFunctionArgs(bool require_identifiers) {
  std::vector<FunctionArg> args;
  Expect(TokenKind::kLParen);
  if (Check(TokenKind::kRParen)) {
    Consume();
    return args;
  }
  Direction sticky_dir = Direction::kInput;
  bool seen_default = false;
  DataType prev_data_type;  // §13.3 sticky data-type for inheritance.
  bool first_arg = true;
  do {
    FunctionArg arg;
    // §8.3: class_constructor_arg ::= tf_port_item | default
    if (Check(TokenKind::kKwDefault)) {
      if (seen_default) {
        diag_.Error(CurrentLoc(),
                    "'default' keyword shall appear at most once "
                    "in a class constructor argument list");
      }
      seen_default = true;
      arg.is_default = true;
      Consume();
      args.push_back(arg);
      continue;
    }
    if (Match(TokenKind::kKwConst)) {
      arg.is_const = true;
    }
    bool dir_explicit = false;
    sticky_dir = ParseArgDirection(arg, sticky_dir, &dir_explicit);
    // §13.3: "The const and static qualifiers on the ref direction are
    // included in this default." When direction is inherited from the
    // previous formal (sticky) and that formal carried the ref-side
    // qualifiers, propagate them to the current formal.
    if (!dir_explicit && arg.direction == Direction::kRef && !args.empty()) {
      const auto& prev = args.back();
      if (prev.direction == Direction::kRef) {
        arg.is_const = arg.is_const || prev.is_const;
        arg.is_ref_static = arg.is_ref_static || prev.is_ref_static;
      }
    }
    Match(TokenKind::kKwVar);  // A.2.7 tf_port_item: [var]
    arg.data_type = ParseDataType();
    // §13.3: "Each formal argument has a data type that can be explicitly
    // declared or inherited from the previous argument. If the data type is
    // not explicitly declared, then the default data type is logic if it is
    // the first argument or if the argument direction is explicitly
    // specified. Otherwise, the data type is inherited from the previous
    // argument." kImplicit here means no data_type token was consumed; treat
    // as "not explicitly declared" for the §13.3 rule. §6.8 gives the
    // canonical implicit-data-type → logic mapping that we apply at first
    // position or after an explicit direction keyword.
    if (arg.data_type.kind == DataTypeKind::kImplicit &&
        arg.data_type.packed_dim_left == nullptr && !arg.data_type.is_signed) {
      if (first_arg || dir_explicit) {
        arg.data_type.kind = DataTypeKind::kLogic;
      } else {
        arg.data_type = prev_data_type;
      }
    }
    if (CheckIdentifier()) {
      arg.name = Consume().text;
    } else if (require_identifiers) {
      // §13.3 footnote 28: "In a tf_port_item, it shall be illegal to omit
      // the explicit port_identifier except within a function_prototype or
      // task_prototype."
      diag_.Error(CurrentLoc(),
                  "tf_port_item shall include a port_identifier outside of a "
                  "function_prototype or task_prototype");
    }
    ParseUnpackedDims(arg.unpacked_dims);
    if (Match(TokenKind::kEq)) {
      arg.default_value = ParseExpr();
    }
    prev_data_type = arg.data_type;
    first_arg = false;
    args.push_back(arg);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kRParen);
  return args;
}

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

// A.2.6: Parse a single colon-prefixed specifier pair.
void Parser::ParseOneOverrideSpecifier(ModuleItem* item) {
  if (Match(TokenKind::kKwInitial)) {
    if (item) item->is_method_initial = true;
  } else if (Match(TokenKind::kKwExtends)) {
    if (item) item->is_method_extends = true;
  } else if (Match(TokenKind::kKwFinal)) {
    if (item) item->is_method_final = true;
  }
}

// A.2.6: dynamic_override_specifiers
void Parser::ParseDynamicOverrideSpecifiers(ModuleItem* item) {
  if (Match(TokenKind::kColon)) {
    ParseOneOverrideSpecifier(item);
  }
  if (Match(TokenKind::kColon)) {
    if (Match(TokenKind::kKwFinal)) {
      if (item) item->is_method_final = true;
    }
  }
}

// Parse function/task name with optional class_scope and 'new' for ctors.
void Parser::ParseFuncName(ModuleItem* item) {
  item->return_type = ParseFunctionReturnType();
  // A.1.11: function [class_scope] new — if the return type was parsed as a
  // named type but :: follows, the "type" was actually a class scope prefix.
  if (item->return_type.kind == DataTypeKind::kNamed &&
      Check(TokenKind::kColonColon)) {
    // §8.24: The "type" is actually the class scope prefix.
    item->method_class = item->return_type.type_name;
    item->return_type = DataType{};
    Consume();  // ::
    item->name =
        Match(TokenKind::kKwNew) ? "new" : Expect(TokenKind::kIdentifier).text;
  } else {
    item->name =
        Match(TokenKind::kKwNew) ? "new" : Expect(TokenKind::kIdentifier).text;
  }
  // §8.24 out-of-block methods: class_name::method_name
  while (Match(TokenKind::kColonColon)) {
    item->method_class = item->name;
    item->name =
        Match(TokenKind::kKwNew) ? "new" : Expect(TokenKind::kIdentifier).text;
  }
  // §25.7 interface subroutine bodies: interface_identifier . function_identifier
  if (Match(TokenKind::kDot)) {
    item->method_class = item->name;
    item->name = Expect(TokenKind::kIdentifier).text;
  }
}

// Parse function body: old-style ports, statements, endfunction label.
void Parser::ParseFuncBody(ModuleItem* item) {
  ParseOldStylePortDecls(item, TokenKind::kKwEndfunction);
  while (!Check(TokenKind::kKwEndfunction) && !AtEnd()) {
    if (IsBlockVarDeclStart()) {
      ParseBlockVarDecls(item->func_body_stmts);
    } else {
      item->func_body_stmts.push_back(ParseStmt());
    }
  }
  Expect(TokenKind::kKwEndfunction);
  if (Match(TokenKind::kColon)) {
    std::string_view end_name;
    SourceLoc end_loc = CurrentLoc();
    if (Match(TokenKind::kKwNew)) {
      end_name = "new";
    } else {
      auto end_id = ExpectIdentifier();
      end_name = end_id.text;
      end_loc = end_id.loc;
    }
    if (end_name != item->name) {
      diag_.Error(end_loc, "end label '" + std::string(end_name) +
                               "' does not match '" +
                               std::string(item->name) + "'");
    }
  }
}

ModuleItem* Parser::ParseFunctionDecl(bool prototype_only) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kFunctionDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwFunction);

  ParseDynamicOverrideSpecifiers(item);

  item->is_automatic = Match(TokenKind::kKwAutomatic);
  if (!item->is_automatic) item->is_static = Match(TokenKind::kKwStatic);

  ParseFuncName(item);

  if (Check(TokenKind::kLParen)) {
    item->func_args = ParseFunctionArgs(/*require_identifiers=*/!prototype_only);
    item->is_ansi_ports = true;
  }
  Expect(TokenKind::kSemicolon);

  if (!prototype_only) ParseFuncBody(item);
  return item;
}

ModuleItem* Parser::ParseTaskDecl(bool prototype_only) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kTaskDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwTask);

  ParseDynamicOverrideSpecifiers(item);

  if (Match(TokenKind::kKwAutomatic)) {
    item->is_automatic = true;
  } else if (Match(TokenKind::kKwStatic)) {
    item->is_static = true;
  }

  item->name = Expect(TokenKind::kIdentifier).text;
  // §25.7 interface subroutine bodies: interface_identifier . task_identifier
  if (Match(TokenKind::kDot)) {
    item->method_class = item->name;
    item->name = Expect(TokenKind::kIdentifier).text;
  }
  // §8.24 out-of-block methods: class_name::method_name
  while (Match(TokenKind::kColonColon)) {
    item->method_class = item->name;
    item->name = Expect(TokenKind::kIdentifier).text;
  }

  if (Check(TokenKind::kLParen)) {
    item->func_args = ParseFunctionArgs(/*require_identifiers=*/!prototype_only);
    item->is_ansi_ports = true;
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
  MatchEndLabel(item->name);
  return item;
}

// §A.6.5: Check whether the token after '(' starts a parenthesized
// event_expression.  Unambiguous when it is an edge keyword or another '('.
static bool IsEventExprStart(TokenKind kind) {
  return kind == TokenKind::kKwPosedge || kind == TokenKind::kKwNegedge ||
         kind == TokenKind::kKwEdge || kind == TokenKind::kLParen;
}

std::vector<EventExpr> Parser::ParseEventList() {
  std::vector<EventExpr> events;
  auto parse_event_or_group = [&]() {
    if (Check(TokenKind::kLParen)) {
      auto saved = lexer_.SavePos();
      Consume();  // consume '('
      if (IsEventExprStart(CurrentToken().kind)) {
        // ( event_expression )
        auto sub = ParseEventList();
        events.insert(events.end(), sub.begin(), sub.end());
        Expect(TokenKind::kRParen);
        return;
      }
      lexer_.RestorePos(saved);
    }
    events.push_back(ParseSingleEvent());
  };
  parse_event_or_group();
  while (Match(TokenKind::kKwOr) || Match(TokenKind::kComma)) {
    parse_event_or_group();
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

// --- Old-style port declarations (§13.3 / A.2.7) ---

void Parser::ParseOldStylePortDecls(ModuleItem* item, TokenKind end_kw) {
  while (Check(TokenKind::kKwInput) || Check(TokenKind::kKwOutput) ||
         Check(TokenKind::kKwInout) || Check(TokenKind::kKwRef) ||
         Check(TokenKind::kKwConst)) {
    Direction dir = Direction::kNone;
    bool is_const = Match(TokenKind::kKwConst);  // A.2.7: [const] ref
    if (Check(TokenKind::kKwInput)) {
      dir = Direction::kInput;
    } else if (Check(TokenKind::kKwOutput)) {
      dir = Direction::kOutput;
    } else if (Check(TokenKind::kKwInout)) {
      dir = Direction::kInout;
    } else {
      dir = Direction::kRef;
    }
    Consume();
    bool is_ref_static = (dir == Direction::kRef) && Match(TokenKind::kKwStatic);
    Match(TokenKind::kKwVar);  // A.2.7 tf_port_declaration: [var]
    DataType dt = ParseDataType();
    // §13.3: every old-style tf_port_declaration carries an explicit direction
    // keyword, so the §13.3 rule "default data type is logic if ... the
    // argument direction is explicitly specified" applies whenever the type
    // was omitted. The §6.8 implicit-data-type → logic mapping is the same
    // resolution used for ANSI tf_port_items in ParseFunctionArgs above.
    if (dt.kind == DataTypeKind::kImplicit && dt.packed_dim_left == nullptr &&
        !dt.is_signed) {
      dt.kind = DataTypeKind::kLogic;
    }
    // list_of_tf_variable_identifiers: comma-separated port names
    do {
      FunctionArg arg;
      arg.is_const = is_const;
      arg.is_ref_static = is_ref_static;
      arg.direction = dir;
      arg.data_type = dt;
      arg.name = Expect(TokenKind::kIdentifier).text;
      ParseUnpackedDims(arg.unpacked_dims);
      if (Match(TokenKind::kEq)) {
        arg.default_value = ParseExpr();
      }
      item->func_args.push_back(arg);
    } while (Match(TokenKind::kComma));
    Expect(TokenKind::kSemicolon);
  }
  (void)end_kw;
}

}  // namespace delta
