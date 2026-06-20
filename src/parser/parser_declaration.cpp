#include <optional>

#include "parser/parser.h"

namespace delta {

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

DataType Parser::ParseEnumType() {
  DataType dtype;
  dtype.kind = DataTypeKind::kEnum;
  Expect(TokenKind::kKwEnum);

  auto base = ParseDataType();
  if (base.kind != DataTypeKind::kImplicit) {
    dtype.is_signed = base.is_signed;
    dtype.packed_dim_left = base.packed_dim_left;
    dtype.packed_dim_right = base.packed_dim_right;

    dtype.enum_base_kind = base.kind;

    if (base.kind == DataTypeKind::kNamed) {
      dtype.enum_base_name = base.type_name;
    }
  }

  dtype = ParseEnumBody(dtype);

  return dtype;
}

DataType Parser::ParseEnumBody(const DataType& base) {
  DataType dtype = base;
  Expect(TokenKind::kLBrace);
  do {
    EnumMember member;
    member.name = Expect(TokenKind::kIdentifier).text;

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

DataType Parser::ParseStructOrUnionType() {
  DataType dtype;
  dtype.kind = Check(TokenKind::kKwStruct) ? DataTypeKind::kStruct
                                           : DataTypeKind::kUnion;
  Consume();

  // §7.3.2: a union may carry at most one of the 'soft'/'tagged' qualifiers;
  // diagnose and discard a stray second qualifier.
  auto reject_dup_union_qualifier = [&](TokenKind other) {
    if (!Check(other)) return;
    diag_.Error(CurrentLoc(),
                "union may have at most one of 'soft' or 'tagged'");
    Consume();
  };
  if (dtype.kind == DataTypeKind::kUnion) {
    if (Match(TokenKind::kKwTagged)) {
      dtype.is_tagged = true;
      reject_dup_union_qualifier(TokenKind::kKwSoft);
    } else if (Match(TokenKind::kKwSoft)) {
      dtype.is_soft = true;
      reject_dup_union_qualifier(TokenKind::kKwTagged);
    }
  }

  if (Match(TokenKind::kKwPacked)) {
    dtype.is_packed = true;
    if (Match(TokenKind::kKwSigned)) {
      dtype.is_signed = true;
    } else {
      Match(TokenKind::kKwUnsigned);
    }
  }

  if (CheckIdentifier() && !Check(TokenKind::kLBrace)) {
    diag_.Error(CurrentLoc(),
                dtype.kind == DataTypeKind::kStruct
                    ? "structure declarations may not have a tag before '{'"
                    : "union declarations may not have a tag before '{'");
    Consume();
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
  auto open_brace_loc = CurrentLoc();
  Expect(TokenKind::kLBrace);

  // Parse the data_type that prefixes a struct/union member declaration,
  // including any nested struct/union/enum with its packed dimensions.
  auto parse_member_type = [&]() {
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
    return member_type;
  };

  // Parse the comma-separated list of declarators sharing one member type.
  auto parse_member_list = [&](const DataType& member_type,
                               const std::vector<Attribute>& member_attrs,
                               bool is_rand, bool is_randc) {
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
      member.type_name = member_type.type_name;
      member.name = Expect(TokenKind::kIdentifier).text;
      ParseUnpackedDims(member.unpacked_dims);
      if (Match(TokenKind::kEq)) {
        member.init_expr = ParseExpr();
      }
      dtype.struct_members.push_back(member);
    } while (Match(TokenKind::kComma));
    Expect(TokenKind::kSemicolon);
  };

  while (!Check(TokenKind::kRBrace) && !AtEnd()) {
    auto member_attrs = ParseAttributes();
    bool is_rand = Match(TokenKind::kKwRand);
    bool is_randc = !is_rand && Match(TokenKind::kKwRandc);

    DataType member_type = parse_member_type();
    if (member_type.kind == DataTypeKind::kImplicit && !CheckIdentifier()) {
      Synchronize();
      continue;
    }
    parse_member_list(member_type, member_attrs, is_rand, is_randc);
  }
  if (dtype.struct_members.empty()) {
    diag_.Error(open_brace_loc,
                dtype.kind == DataTypeKind::kStruct
                    ? "struct body must contain at least one member"
                    : "union body must contain at least one member");
  }
  Expect(TokenKind::kRBrace);
}

ModuleItem* Parser::ParseTypedef() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kTypedef;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwTypedef);

  // Forward class/interface typedef: `typedef class foo;` (§6.18).
  auto try_forward_class = [&]() -> bool {
    if (!Check(TokenKind::kKwClass) && !Check(TokenKind::kKwInterface)) {
      return false;
    }
    Consume();
    if (Check(TokenKind::kKwClass)) Consume();
    item->name = Expect(TokenKind::kIdentifier).text;
    known_types_.insert(item->name);
    Expect(TokenKind::kSemicolon);
    return true;
  };

  // Forward enum/struct/union typedef: `typedef struct foo;` (§6.18). Leaves
  // the lexer position unchanged when the form does not match.
  auto try_forward_aggregate = [&]() -> bool {
    if (!Check(TokenKind::kKwEnum) && !Check(TokenKind::kKwStruct) &&
        !Check(TokenKind::kKwUnion)) {
      return false;
    }
    auto saved = lexer_.SavePos();
    DataTypeKind fwd_kind = DataTypeKind::kImplicit;
    switch (CurrentToken().kind) {
      case TokenKind::kKwEnum:
        fwd_kind = DataTypeKind::kEnum;
        break;
      case TokenKind::kKwStruct:
        fwd_kind = DataTypeKind::kStruct;
        break;
      case TokenKind::kKwUnion:
        fwd_kind = DataTypeKind::kUnion;
        break;
      default:
        break;
    }
    Consume();
    if (CheckIdentifier()) {
      auto id_saved = lexer_.SavePos();
      auto id_tok = Consume();
      if (Check(TokenKind::kSemicolon)) {
        item->name = id_tok.text;
        item->forward_type_kind = fwd_kind;
        known_types_.insert(item->name);
        Expect(TokenKind::kSemicolon);
        return true;
      }
      lexer_.RestorePos(id_saved);
    }
    lexer_.RestorePos(saved);
    return false;
  };

  // Forward bare typedef: `typedef foo;` (§6.18).
  auto try_forward_bare = [&]() -> bool {
    if (!CheckIdentifier()) return false;
    auto saved = lexer_.SavePos();
    auto id_tok = Consume();
    if (Check(TokenKind::kSemicolon)) {
      item->name = id_tok.text;
      known_types_.insert(item->name);
      Expect(TokenKind::kSemicolon);
      return true;
    }
    lexer_.RestorePos(saved);
    return false;
  };

  // Skip a (possibly nested) run of bracketed unpacked-dimension tokens while
  // probing for the interface-port '.'-form below.
  auto skip_bracketed_dims = [&]() {
    while (Check(TokenKind::kLBracket)) {
      Consume();
      int depth = 1;
      while (depth > 0 && !Check(TokenKind::kEof)) {
        if (CurrentToken().kind == TokenKind::kLBracket)
          depth++;
        else if (CurrentToken().kind == TokenKind::kRBracket)
          depth--;
        if (depth > 0) Consume();
      }
      if (Check(TokenKind::kRBracket)) Consume();
    }
  };

  // Interface-port typedef: `typedef intf.T name;` (§6.18).
  auto try_interface_port = [&]() -> bool {
    if (!CheckIdentifier()) return false;
    auto saved = lexer_.SavePos();
    Consume();
    skip_bracketed_dims();
    if (!Check(TokenKind::kDot)) {
      lexer_.RestorePos(saved);
      return false;
    }
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
    return true;
  };

  if (try_forward_class()) return item;
  if (try_forward_aggregate()) return item;
  if (try_forward_bare()) return item;
  if (try_interface_port()) return item;

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

  if (Check(TokenKind::kKwWith)) {
    Consume();
    auto func_name = Expect(TokenKind::kIdentifier).text;
    if (Match(TokenKind::kColonColon)) {
      item->nettype_resolve_func = Expect(TokenKind::kIdentifier).text;
    } else {
      item->nettype_resolve_func = func_name;
    }
  }
  known_types_.insert(item->name);
  known_nettypes_.insert(item->name);
  Expect(TokenKind::kSemicolon);
  return item;
}

Direction Parser::ParseArgDirection(FunctionArg& arg, Direction sticky_dir,
                                    bool* was_explicit) {
  if (was_explicit) *was_explicit = true;
  auto reject_extra_direction = [&](Direction first) {
    while (Check(TokenKind::kKwRef) || Check(TokenKind::kKwInput) ||
           Check(TokenKind::kKwOutput) || Check(TokenKind::kKwInout)) {
      bool involves_ref = first == Direction::kRef || Check(TokenKind::kKwRef);
      if (!involves_ref) break;
      diag_.Error(CurrentLoc(),
                  "combining ref with another directional qualifier is "
                  "illegal");
      Consume();
      Match(TokenKind::kKwStatic);
    }
  };
  if (Check(TokenKind::kKwInput)) {
    arg.direction = Direction::kInput;
    Consume();
    reject_extra_direction(Direction::kInput);
    return Direction::kInput;
  }
  if (Check(TokenKind::kKwOutput)) {
    arg.direction = Direction::kOutput;
    Consume();
    reject_extra_direction(Direction::kOutput);
    return Direction::kOutput;
  }
  if (Check(TokenKind::kKwInout)) {
    arg.direction = Direction::kInout;
    Consume();
    reject_extra_direction(Direction::kInout);
    return Direction::kInout;
  }
  if (Check(TokenKind::kKwRef)) {
    arg.direction = Direction::kRef;
    Consume();
    arg.is_ref_static = Match(TokenKind::kKwStatic);
    reject_extra_direction(Direction::kRef);
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
  DataType prev_data_type;
  bool first_arg = true;
  // §8.17: an argument that directly follows the 'default' keyword in a
  // constructor argument list does not inherit the preceding argument's
  // direction or data type; it falls back to the default direction (input)
  // and default data type (logic).
  bool prev_was_default = false;

  // §8.17: a tf_port_item with no explicit direction that is 'ref' inherits the
  // const/static qualifiers of the immediately preceding 'ref' argument.
  auto inherit_ref_qualifiers = [&](FunctionArg& arg, bool dir_explicit) {
    if (dir_explicit || arg.direction != Direction::kRef || args.empty())
      return;
    const auto& prev = args.back();
    if (prev.direction != Direction::kRef) return;
    arg.is_const = arg.is_const || prev.is_const;
    arg.is_ref_static = arg.is_ref_static || prev.is_ref_static;
  };

  // §8.17: resolve an implicit tf_port data type — the first argument and any
  // argument with an explicit direction (or following 'default') default to
  // logic; otherwise it inherits the previous argument's data type.
  auto resolve_implicit_data_type = [&](FunctionArg& arg, bool dir_explicit) {
    if (arg.data_type.kind != DataTypeKind::kImplicit ||
        arg.data_type.packed_dim_left != nullptr || arg.data_type.is_signed) {
      return;
    }
    if (first_arg || dir_explicit || prev_was_default) {
      arg.data_type.kind = DataTypeKind::kLogic;
    } else {
      arg.data_type = prev_data_type;
    }
  };

  // §8.17: the 'default' sentinel in a class constructor argument list. Records
  // a default placeholder argument; returns true when consumed so the caller
  // skips to the next argument.
  auto try_parse_default_sentinel = [&]() -> bool {
    if (!Check(TokenKind::kKwDefault)) return false;
    if (seen_default) {
      diag_.Error(CurrentLoc(),
                  "'default' keyword shall appear at most once "
                  "in a class constructor argument list");
    }
    seen_default = true;
    FunctionArg arg;
    arg.is_default = true;
    Consume();
    args.push_back(arg);
    prev_was_default = true;
    return true;
  };

  // tf_port_item trailer: the port identifier, unpacked dimensions, and an
  // optional default value (§13.3 / §8.17).
  auto parse_arg_trailer = [&](FunctionArg& arg) {
    if (CheckIdentifier()) {
      arg.name = Consume().text;
    } else if (require_identifiers) {
      diag_.Error(CurrentLoc(),
                  "tf_port_item shall include a port_identifier outside of a "
                  "function_prototype or task_prototype");
    }
    ParseUnpackedDims(arg.unpacked_dims);
    if (Match(TokenKind::kEq)) {
      arg.default_value = ParseExpr();
    }
  };

  do {
    // tf_port_item permits a leading attribute_instance list; consume and
    // discard any such list before the rest of the port item.
    if (Check(TokenKind::kAttrStart)) {
      ParseAttributes();
    }

    if (try_parse_default_sentinel()) continue;

    FunctionArg arg;
    if (Match(TokenKind::kKwConst)) {
      arg.is_const = true;
    }
    // §8.17: the argument following 'default' starts from the default
    // direction (input) rather than inheriting the previous argument's
    // direction via stickiness.
    if (prev_was_default) sticky_dir = Direction::kInput;
    bool dir_explicit = false;
    sticky_dir = ParseArgDirection(arg, sticky_dir, &dir_explicit);

    inherit_ref_qualifiers(arg, dir_explicit);
    Match(TokenKind::kKwVar);
    arg.data_type = ParseDataType();
    resolve_implicit_data_type(arg, dir_explicit);

    parse_arg_trailer(arg);
    prev_data_type = arg.data_type;
    first_arg = false;
    prev_was_default = false;
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
    ParsePackedDims(dt);
    return dt;
  }
  return ParseDataType();
}

void Parser::ParseOneOverrideSpecifier(ModuleItem* item) {
  if (Match(TokenKind::kKwInitial)) {
    if (item) item->is_method_initial = true;
  } else if (Match(TokenKind::kKwExtends)) {
    if (item) item->is_method_extends = true;
  } else if (Match(TokenKind::kKwFinal)) {
    if (item) item->is_method_final = true;
  }
}

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

void Parser::ParseFuncName(ModuleItem* item) {
  item->return_type = ParseFunctionReturnType();

  if (item->return_type.kind == DataTypeKind::kNamed &&
      Check(TokenKind::kColonColon)) {
    item->method_class = item->return_type.type_name;
    item->return_type = DataType{};
    Consume();
    item->name =
        Match(TokenKind::kKwNew) ? "new" : Expect(TokenKind::kIdentifier).text;
  } else {
    item->name =
        Match(TokenKind::kKwNew) ? "new" : Expect(TokenKind::kIdentifier).text;
  }

  while (Match(TokenKind::kColonColon)) {
    item->method_class = item->name;
    item->name =
        Match(TokenKind::kKwNew) ? "new" : Expect(TokenKind::kIdentifier).text;
  }

  if (Match(TokenKind::kDot)) {
    item->method_class = item->name;
    item->name = Expect(TokenKind::kIdentifier).text;
  }
}

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
                               "' does not match '" + std::string(item->name) +
                               "'");
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
    item->func_args = ParseFunctionArgs(!prototype_only);
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

  if (Match(TokenKind::kDot)) {
    item->method_class = item->name;
    item->name = Expect(TokenKind::kIdentifier).text;
  }

  while (Match(TokenKind::kColonColon)) {
    item->method_class = item->name;
    item->name = Expect(TokenKind::kIdentifier).text;
  }

  if (Check(TokenKind::kLParen)) {
    item->func_args = ParseFunctionArgs(!prototype_only);
    item->is_ansi_ports = true;
  }
  Expect(TokenKind::kSemicolon);

  if (prototype_only) return item;

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

static bool IsEventExprStart(TokenKind kind) {
  return kind == TokenKind::kKwPosedge || kind == TokenKind::kKwNegedge ||
         kind == TokenKind::kKwEdge || kind == TokenKind::kLParen;
}

std::vector<EventExpr> Parser::ParseEventList() {
  std::vector<EventExpr> events;
  auto parse_event_or_group = [&]() {
    if (Check(TokenKind::kLParen)) {
      auto saved = lexer_.SavePos();
      Consume();
      if (IsEventExprStart(CurrentToken().kind)) {
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

  if (Match(TokenKind::kKwIff)) {
    ev.iff_condition = ParseExpr();
  }
  return ev;
}

void Parser::ParseOldStylePortDecls(ModuleItem* item, TokenKind end_kw) {
  // Consume the leading direction keyword of a tf_port_declaration. The 'const'
  // qualifier (already consumed by the caller) is mapped to 'ref'.
  auto parse_port_direction = [&]() -> Direction {
    if (Check(TokenKind::kKwInput)) {
      Consume();
      return Direction::kInput;
    }
    if (Check(TokenKind::kKwOutput)) {
      Consume();
      return Direction::kOutput;
    }
    if (Check(TokenKind::kKwInout)) {
      Consume();
      return Direction::kInout;
    }
    Consume();
    return Direction::kRef;
  };

  // Parse the comma-separated declarators that share one tf_port_declaration
  // header (direction/const/static and data type).
  auto parse_port_declarators = [&](Direction dir, bool is_const,
                                    bool is_ref_static, const DataType& dt) {
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
  };

  while (true) {
    // tf_port_declaration permits a leading attribute_instance list. Peek
    // past any attributes and only commit to the declaration if a direction
    // (or const) keyword follows.
    auto saved = lexer_.SavePos();
    if (Check(TokenKind::kAttrStart)) {
      ParseAttributes();
    }
    if (!(Check(TokenKind::kKwInput) || Check(TokenKind::kKwOutput) ||
          Check(TokenKind::kKwInout) || Check(TokenKind::kKwRef) ||
          Check(TokenKind::kKwConst))) {
      lexer_.RestorePos(saved);
      break;
    }
    bool is_const = Match(TokenKind::kKwConst);
    Direction dir = parse_port_direction();
    bool is_ref_static =
        (dir == Direction::kRef) && Match(TokenKind::kKwStatic);
    Match(TokenKind::kKwVar);
    DataType dt = ParseDataType();

    if (dt.kind == DataTypeKind::kImplicit && dt.packed_dim_left == nullptr &&
        !dt.is_signed) {
      dt.kind = DataTypeKind::kLogic;
    }

    parse_port_declarators(dir, is_const, is_ref_static, dt);
  }
  (void)end_kw;
}

}  // namespace delta
