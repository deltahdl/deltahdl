#include "parser/parser.h"

namespace delta {

ModuleDecl* Parser::ParseInterfaceDecl() {
  auto* decl = arena_.Create<ModuleDecl>();
  decl->decl_kind = ModuleDeclKind::kInterface;
  decl->range.start = CurrentLoc();
  Expect(TokenKind::kKwInterface);

  decl->is_automatic = Match(TokenKind::kKwAutomatic);
  if (!decl->is_automatic) Match(TokenKind::kKwStatic);

  decl->name = Expect(TokenKind::kIdentifier).text;
  ParseParamsPortsAndSemicolon(*decl);

  auto* prev_module = current_module_;
  current_module_ = decl;
  bool non_ansi =
      !decl->ports.empty() && decl->ports[0].direction == Direction::kNone;
  while (!Check(TokenKind::kKwEndinterface) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    if (Check(TokenKind::kKwModport)) {
      ParseModportDecl(decl->modports);
    } else if (non_ansi && IsPortDirection(CurrentToken().kind)) {
      ParseNonAnsiPortDecls(*decl);
    } else {
      ParseModuleItem(decl->items);
    }
  }
  current_module_ = prev_module;
  Expect(TokenKind::kKwEndinterface);
  MatchEndLabel(decl->name);
  decl->range.end = CurrentLoc();
  return decl;
}

ModportPort Parser::ParseModportTfPort(bool is_import) {
  ModportPort port;
  port.is_import = is_import;
  port.is_export = !is_import;
  if (Check(TokenKind::kKwTask)) {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kTaskDecl;
    item->loc = CurrentLoc();
    Consume();
    item->name = Expect(TokenKind::kIdentifier).text;
    if (Check(TokenKind::kLParen))

      item->func_args = ParseFunctionArgs( false);
    port.prototype = item;
    port.name = item->name;
  } else if (Check(TokenKind::kKwFunction)) {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kFunctionDecl;
    item->loc = CurrentLoc();
    Consume();
    item->data_type = ParseFunctionReturnType();
    item->name = Expect(TokenKind::kIdentifier).text;
    if (Check(TokenKind::kLParen))

      item->func_args = ParseFunctionArgs( false);
    port.prototype = item;
    port.name = item->name;
  } else {
    port.name = Expect(TokenKind::kIdentifier).text;
  }
  return port;
}

ModportPort Parser::ParseModportSimplePort(Direction dir) {
  ModportPort port;
  port.direction = dir;
  if (Match(TokenKind::kDot)) {
    port.name = Expect(TokenKind::kIdentifier).text;
    Expect(TokenKind::kLParen);
    if (!Check(TokenKind::kRParen)) port.expr = ParseExpr();
    Expect(TokenKind::kRParen);
  } else {
    port.name = Expect(TokenKind::kIdentifier).text;
  }
  return port;
}

static Direction TokenToDirection(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwInput:
      return Direction::kInput;
    case TokenKind::kKwOutput:
      return Direction::kOutput;
    case TokenKind::kKwInout:
      return Direction::kInout;
    case TokenKind::kKwRef:
      return Direction::kRef;
    default:
      return Direction::kNone;
  }
}

void Parser::ParseModportItem(ModportDecl* mp) {
  Direction cur_dir = Direction::kNone;

  int tf_mode = 0;
  while (!Check(TokenKind::kRParen) && !AtEnd()) {
    ParseAttributes();
    if (Check(TokenKind::kKwClocking)) {
      tf_mode = 0;
      Consume();
      ModportPort port;
      port.is_clocking = true;
      port.name = Expect(TokenKind::kIdentifier).text;
      mp->ports.push_back(port);
    } else if (Check(TokenKind::kKwImport) || Check(TokenKind::kKwExport)) {
      tf_mode = Check(TokenKind::kKwImport) ? 1 : 2;
      Consume();
      mp->ports.push_back(ParseModportTfPort(tf_mode == 1));
    } else if (IsPortDirection(CurrentToken().kind)) {
      tf_mode = 0;
      cur_dir = TokenToDirection(CurrentToken().kind);
      Consume();
      mp->ports.push_back(ParseModportSimplePort(cur_dir));
    } else if (tf_mode != 0) {
      mp->ports.push_back(ParseModportTfPort(tf_mode == 1));
    } else {
      mp->ports.push_back(ParseModportSimplePort(cur_dir));
    }
    if (!Check(TokenKind::kRParen)) Expect(TokenKind::kComma);
  }
}

void Parser::ParseModportDecl(std::vector<ModportDecl*>& out) {
  Expect(TokenKind::kKwModport);
  do {
    auto* mp = arena_.Create<ModportDecl>();
    mp->loc = CurrentLoc();
    mp->name = Expect(TokenKind::kIdentifier).text;
    Expect(TokenKind::kLParen);
    ParseModportItem(mp);
    Expect(TokenKind::kRParen);
    out.push_back(mp);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
}

ModuleDecl* Parser::ParseProgramDecl() {
  auto* decl = arena_.Create<ModuleDecl>();
  decl->decl_kind = ModuleDeclKind::kProgram;
  decl->range.start = CurrentLoc();
  Expect(TokenKind::kKwProgram);

  decl->is_automatic = Match(TokenKind::kKwAutomatic);
  if (!decl->is_automatic) Match(TokenKind::kKwStatic);

  decl->name = Expect(TokenKind::kIdentifier).text;
  ParseParamsPortsAndSemicolon(*decl);

  auto* prev_module = current_module_;
  current_module_ = decl;
  bool non_ansi =
      !decl->ports.empty() && decl->ports[0].direction == Direction::kNone;
  while (!Check(TokenKind::kKwEndprogram) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    if (non_ansi && IsPortDirection(CurrentToken().kind)) {
      ParseNonAnsiPortDecls(*decl);
    } else {
      ParseModuleItem(decl->items);
    }
  }
  current_module_ = prev_module;
  Expect(TokenKind::kKwEndprogram);
  MatchEndLabel(decl->name);
  decl->range.end = CurrentLoc();
  return decl;
}

void Parser::ParseExtendsArgList(ClassDecl* decl) {
  Consume();
  if (Match(TokenKind::kKwDefault)) {
    decl->extends_has_default = true;
  } else if (!Check(TokenKind::kRParen)) {
    do {
      decl->extends_args.push_back(ParseExpr());
    } while (Match(TokenKind::kComma));
  }
  Expect(TokenKind::kRParen);
}

void Parser::ParseClassExtendsClause(ClassDecl* decl, bool is_implements) {

  do {
    auto name = Expect(TokenKind::kIdentifier).text;
    while (Match(TokenKind::kColonColon)) {
      name = Expect(TokenKind::kIdentifier).text;
    }
    bool is_first_base = !is_implements && decl->base_class.empty();
    if (is_first_base) {
      decl->base_class = name;
    }
    std::vector<DataType> tparams;
    if (Check(TokenKind::kHash)) {
      Consume();
      tparams = ParseTypeParamList();
      if (is_first_base) {
        decl->base_class_type_params = tparams;
      }
    }
    if (is_implements) {
      decl->implements_types.push_back({name, std::move(tparams)});
    } else if (!is_first_base) {
      decl->extends_interfaces.push_back({name, std::move(tparams)});
    }

    if (Check(TokenKind::kLParen)) {
      if (is_implements) {
        std::vector<Expr*> discard;
        ParseParenList(discard);
      } else {
        ParseExtendsArgList(decl);
      }
    }
  } while (Match(TokenKind::kComma));
}

ClassDecl* Parser::ParseClassDecl() {
  auto* decl = arena_.Create<ClassDecl>();
  decl->range.start = CurrentLoc();
  decl->is_virtual = Match(TokenKind::kKwVirtual);
  decl->is_interface = Match(TokenKind::kKwInterface);
  Expect(TokenKind::kKwClass);

  if (Match(TokenKind::kColon)) {
    Expect(TokenKind::kKwFinal);
    decl->is_final = true;
  }
  Match(TokenKind::kKwAutomatic);
  Match(TokenKind::kKwStatic);
  decl->name = Expect(TokenKind::kIdentifier).text;
  known_types_.insert(decl->name);

  if (Check(TokenKind::kHash)) {
    Consume();
    Expect(TokenKind::kLParen);
    bool is_lp_group = false;
    while (!Check(TokenKind::kRParen) && !AtEnd()) {
      ParseParamPortDecl(decl->params, decl->type_param_names,
                         decl->localparam_port_names, is_lp_group);
      Match(TokenKind::kComma);
    }
    Expect(TokenKind::kRParen);
  }

  if (Match(TokenKind::kKwExtends)) ParseClassExtendsClause(decl, false);

  if (Match(TokenKind::kKwImplements)) ParseClassExtendsClause(decl, true);
  Expect(TokenKind::kSemicolon);

  ++class_body_depth_;
  while (!Check(TokenKind::kKwEndclass) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    auto before = lexer_.SavePos().pos;
    ParseClassMembers(decl->members);

    if (lexer_.SavePos().pos == before) Consume();
  }
  --class_body_depth_;
  Expect(TokenKind::kKwEndclass);
  MatchEndLabel(decl->name);
  decl->range.end = CurrentLoc();
  return decl;
}

bool Parser::TryConsumeClassQualifier(ClassMember* m, TokenKind kw,
                                      bool ClassMember::* flag,
                                      const char* dup_msg) {
  if (!Check(kw)) return false;
  if (m->*flag) diag_.Error(CurrentLoc(), dup_msg);
  m->*flag = true;
  Consume();
  return true;
}

bool Parser::TryConsumeAccessQualifier(ClassMember* m) {

  if (Check(TokenKind::kKwLocal)) {
    if (m->is_protected)
      diag_.Error(CurrentLoc(),
                  "cannot combine 'local' and 'protected' qualifiers");
    if (m->is_local) diag_.Error(CurrentLoc(), "duplicate 'local' qualifier");
    m->is_local = true;
    Consume();
    return true;
  }
  if (Check(TokenKind::kKwProtected)) {
    if (m->is_local)
      diag_.Error(CurrentLoc(),
                  "cannot combine 'local' and 'protected' qualifiers");
    if (m->is_protected)
      diag_.Error(CurrentLoc(), "duplicate 'protected' qualifier");
    m->is_protected = true;
    Consume();
    return true;
  }
  return false;
}

bool Parser::TryConsumeRandQualifier(ClassMember* m) {

  if (Check(TokenKind::kKwRand)) {
    if (m->is_randc)
      diag_.Error(CurrentLoc(), "cannot combine 'rand' and 'randc' qualifiers");
    if (m->is_rand) diag_.Error(CurrentLoc(), "duplicate 'rand' qualifier");
    m->is_rand = true;
    Consume();
    return true;
  }
  if (Check(TokenKind::kKwRandc)) {
    if (m->is_rand)
      diag_.Error(CurrentLoc(), "cannot combine 'rand' and 'randc' qualifiers");
    if (m->is_randc) diag_.Error(CurrentLoc(), "duplicate 'randc' qualifier");
    m->is_randc = true;
    Consume();
    return true;
  }
  return false;
}

bool Parser::ParseClassQualifiers(ClassMember* m) {
  bool proto = false;
  while (true) {
    if (TryConsumeAccessQualifier(m)) continue;
    if (TryConsumeClassQualifier(m, TokenKind::kKwStatic,
                                 &ClassMember::is_static,
                                 "duplicate 'static' qualifier"))
      continue;
    if (TryConsumeClassQualifier(m, TokenKind::kKwVirtual,
                                 &ClassMember::is_virtual,
                                 "duplicate 'virtual' qualifier"))
      continue;
    if (Match(TokenKind::kKwPure)) {
      m->is_pure_virtual = true;
      proto = true;
      continue;
    }
    if (TryConsumeRandQualifier(m)) continue;
    if (TryConsumeClassQualifier(m, TokenKind::kKwConst,
                                 &ClassMember::is_const,
                                 "duplicate 'const' qualifier"))
      continue;
    if (Match(TokenKind::kKwExtern)) {
      proto = true;
      // 18.5.1: 'extern constraint name;' is the explicit prototype form. The
      // flag is only meaningful for constraint members.
      m->is_constraint_extern = true;
      continue;
    }
    break;
  }
  return proto;
}

void Parser::ValidateClassMethod(ClassMember* member) {

  if (member->method->is_static) {
    diag_.Error(member->method->loc,
                "class method shall not have static lifetime");
  }

  if (member->is_static && member->is_virtual &&
      member->method->name != "new") {
    diag_.Error(member->method->loc,
                "static method shall not be declared virtual");
  }
  if (member->is_static) member->method->is_static = true;
}

void Parser::ValidateConstructorQualifiers(ClassMember* member) {
  if (member->method->name != "new") return;
  if (member->is_static) {
    diag_.Error(member->method->loc,
                "constructor shall not be declared static");
  }
  if (member->is_virtual) {
    diag_.Error(member->method->loc,
                "constructor shall not be declared virtual");
  }
}

bool Parser::TryParseMethodOrConstraint(std::vector<ClassMember*>& members,
                                        ClassMember* member, bool proto) {
  if (Check(TokenKind::kKwFunction)) {
    member->kind = ClassMemberKind::kMethod;
    member->method = ParseFunctionDecl(proto);
    ValidateClassMethod(member);
    ValidateConstructorQualifiers(member);
    if (proto && !member->is_pure_virtual) member->method->is_extern = true;
    members.push_back(member);
    return true;
  }
  if (Check(TokenKind::kKwTask)) {
    member->kind = ClassMemberKind::kMethod;
    member->method = ParseTaskDecl(proto);
    ValidateClassMethod(member);
    if (proto && !member->is_pure_virtual) member->method->is_extern = true;
    members.push_back(member);
    return true;
  }
  if (Check(TokenKind::kKwConstraint)) {
    members.push_back(ParseConstraintStub(member));
    return true;
  }
  return false;
}

bool Parser::TryParseKeywordClassMember(std::vector<ClassMember*>& members,
                                        ClassMember* member, bool proto) {
  if (TryParseMethodOrConstraint(members, member, proto)) return true;
  if (Check(TokenKind::kKwTypedef)) {
    member->kind = ClassMemberKind::kTypedef;
    member->typedef_item = ParseTypedef();
    member->name = member->typedef_item->name;
    members.push_back(member);
    return true;
  }
  if (Check(TokenKind::kKwParameter) || Check(TokenKind::kKwLocalparam)) {
    std::vector<ModuleItem*> param_items;
    ParseParamDecl(param_items);
    for (size_t i = 0; i < param_items.size(); ++i) {
      auto* m = (i == 0) ? member : arena_.Create<ClassMember>();
      m->kind = ClassMemberKind::kProperty;
      m->name = param_items[i]->name;
      members.push_back(m);
    }
    return true;
  }
  if (IsAtClassDecl()) {
    member->kind = ClassMemberKind::kClassDecl;
    member->nested_class = ParseClassDecl();
    member->name = member->nested_class->name;
    members.push_back(member);
    return true;
  }
  if (Check(TokenKind::kKwCovergroup)) {
    member->kind = ClassMemberKind::kCovergroup;
    std::vector<ModuleItem*> temp;
    ParseCovergroupDecl(temp);
    if (!temp.empty()) {
      member->name = temp[0]->name;
      // §19.4.1: carry the extended base covergroup name onto the class member
      // so a derived embedded covergroup can be recognized in class scope.
      member->covergroup_extends_base = temp[0]->covergroup_extends_base;
    }
    members.push_back(member);
    return true;
  }
  return false;
}

void Parser::ParseClassMembers(std::vector<ClassMember*>& members) {

  ParseAttributes();

  if (Check(TokenKind::kKwImport)) {
    diag_.Error(CurrentLoc(),
                "package import declaration is not allowed in class scope");
    while (!Check(TokenKind::kSemicolon) && !AtEnd()) Consume();
    Match(TokenKind::kSemicolon);
    return;
  }
  // §35.7: a DPI export declaration must live in the scope where the
  // function being exported is defined, so an export inside a class body
  // would have to designate a class member function — explicitly forbidden
  // by the standard's class-member exclusion.
  if (Check(TokenKind::kKwExport)) {
    diag_.Error(CurrentLoc(),
                "DPI export declaration is not allowed in class scope; "
                "class member functions cannot be exported (§35.7)");
    while (!Check(TokenKind::kSemicolon) && !AtEnd()) Consume();
    Match(TokenKind::kSemicolon);
    return;
  }
  auto* member = arena_.Create<ClassMember>();
  member->loc = CurrentLoc();
  bool proto = ParseClassQualifiers(member);

  if (TryParseKeywordClassMember(members, member, proto)) return;

  DataType dtype = ParseDataType();
  member->kind = ClassMemberKind::kProperty;
  member->data_type = dtype;
  member->name = Expect(TokenKind::kIdentifier).text;
  ParseUnpackedDims(member->unpacked_dims);
  if (Match(TokenKind::kEq)) member->init_expr = ParseExpr();
  members.push_back(member);
  ParseExtraPropertyDecls(members, member, dtype);
  Expect(TokenKind::kSemicolon);
}

void Parser::ParseExtraPropertyDecls(std::vector<ClassMember*>& members,
                                     const ClassMember* first,
                                     const DataType& dtype) {
  while (Match(TokenKind::kComma)) {
    auto* extra = arena_.Create<ClassMember>();
    extra->loc = CurrentLoc();
    extra->kind = ClassMemberKind::kProperty;
    extra->data_type = dtype;
    extra->is_rand = first->is_rand;
    extra->is_randc = first->is_randc;
    extra->is_static = first->is_static;
    extra->is_const = first->is_const;
    extra->name = Expect(TokenKind::kIdentifier).text;
    ParseUnpackedDims(extra->unpacked_dims);
    if (Match(TokenKind::kEq)) extra->init_expr = ParseExpr();
    members.push_back(extra);
  }
}

ClassMember* Parser::ParseConstraintStub(ClassMember* member) {
  member->kind = ClassMemberKind::kConstraint;
  Consume();

  if (Match(TokenKind::kColon)) {
    if (Match(TokenKind::kKwInitial)) {
      member->is_constraint_initial = true;
    } else if (Match(TokenKind::kKwExtends)) {
      member->is_constraint_extends = true;
    } else if (Match(TokenKind::kKwFinal)) {
      member->is_constraint_final = true;
    }
  }
  if (Match(TokenKind::kColon)) {
    if (Match(TokenKind::kKwFinal)) member->is_constraint_final = true;
  }
  member->name = Expect(TokenKind::kIdentifier).text;

  // 18.5.1: a constraint with no block is a prototype, completed elsewhere by
  // an external constraint block.
  if (Match(TokenKind::kSemicolon)) {
    member->is_constraint_prototype = true;
    return member;
  }
  Expect(TokenKind::kLBrace);
  int depth = 1;
  while (depth > 0 && !AtEnd()) {
    if (Check(TokenKind::kKwForeach)) {
      // 18.5.7.1: a foreach iterative constraint heads its constraint_set with
      // 'foreach ( array_id [ loop_variables ] )'. Validate that header (in
      // particular the loop-variable naming rule) and record it on the member
      // for the elaborator's dimension check before the surrounding scan
      // resumes over the constraint_set body.
      CheckForeachConstraintHeader(member);
    } else if (Check(TokenKind::kKwDist)) {
      // 18.5.3: 'expression dist { dist_list }'. Hand the brace-enclosed
      // dist_list to a dedicated scan so its default-item rules are enforced.
      Consume();
      CheckDistSet();
    } else if (Match(TokenKind::kLBrace)) {
      ++depth;
    } else if (Match(TokenKind::kRBrace)) {
      --depth;
    } else {
      CheckConstraintExprToken(CurrentToken());
      Consume();
    }
  }
  return member;
}

// 18.5.3: scan a dist_list ('{ dist_item { , dist_item } }') and enforce the
// rules that govern its default specification: it shall use the :/ operator
// (the := operator or an omitted operator is an error), and a distribution
// shall contain at most one default specification.
void Parser::CheckDistSet() {
  if (!Match(TokenKind::kLBrace)) return;
  int depth = 1;
  int default_count = 0;
  while (depth > 0 && !AtEnd()) {
    if (Check(TokenKind::kKwDefault)) {
      Token def = Consume();
      if (++default_count > 1) {
        diag_.Error(def.loc,
                    "a distribution shall contain at most one default "
                    "specification");
      }
      if (CheckColonSlash()) {
        MatchColonSlash();
      } else {
        diag_.Error(def.loc,
                    "a default distribution specification shall use the :/ "
                    "operator");
      }
    } else if (Match(TokenKind::kLBrace)) {
      ++depth;
    } else if (Match(TokenKind::kRBrace)) {
      --depth;
    } else {
      CheckConstraintExprToken(CurrentToken());
      Consume();
    }
  }
}

// Constraint expressions are declarative: 18.3 forbids 4-state values (x or z)
// and 4-state equality operators (=== and !==) inside a constraint, and 18.5
// forbids operators with side effects (++ and --). Both subclauses constrain
// the same constraint_expression construct, so the checks share one scan of
// the constraint block body.
static bool LiteralHasFourStateDigit(std::string_view text) {
  for (char c : text) {
    if (c == 'x' || c == 'X' || c == 'z' || c == 'Z') return true;
  }
  return false;
}

// 18.5.7.1: scan the header of a foreach iterative constraint,
//   foreach ( ps_or_hierarchical_array_identifier [ loop_variables ] )
// where loop_variables is a comma-separated list of optional index variable
// identifiers. The clause makes it an error for a loop variable to reuse the
// identifier of the array being iterated, so take the trailing identifier of
// the (possibly hierarchical) array reference as the array's name and flag any
// loop variable that matches it. Empty loop variables and a trailing run of
// commas are permitted, so an absent identifier between commas is simply
// skipped. The loop-variable count is taken up to the last named slot — a
// trailing run of omittable commas does not inflate it — and recorded, with the
// array name, on the constraint member so the elaborator can check it against
// the array's dimensionality. The constraint_set that follows the header is
// left to the surrounding scan.
void Parser::CheckForeachConstraintHeader(ClassMember* member) {
  SourceLoc foreach_loc = CurrentLoc();
  Consume();  // 'foreach'
  if (!Match(TokenKind::kLParen)) return;
  std::string_view array_name;
  while (!Check(TokenKind::kLBracket) && !Check(TokenKind::kRParen) &&
         !AtEnd()) {
    Token t = Consume();
    if (t.kind == TokenKind::kIdentifier) array_name = t.text;
  }
  int slot = 0;            // 1-based index of the loop-variable slot in view
  int loop_var_count = 0;  // index of the last slot that names a variable
  if (Match(TokenKind::kLBracket)) {
    slot = 1;
    int bracket_depth = 1;
    while (bracket_depth > 0 && !AtEnd()) {
      if (Check(TokenKind::kLBracket)) {
        ++bracket_depth;
        Consume();
      } else if (Check(TokenKind::kRBracket)) {
        --bracket_depth;
        Consume();
      } else if (bracket_depth == 1 && Check(TokenKind::kComma)) {
        ++slot;
        Consume();
      } else {
        Token t = Consume();
        if (bracket_depth == 1 && t.kind == TokenKind::kIdentifier) {
          loop_var_count = slot;
          if (!array_name.empty() && t.text == array_name) {
            diag_.Error(t.loc,
                        std::string("foreach loop variable '") +
                            std::string(t.text) +
                            "' may not have the same name as the array it "
                            "iterates over");
          }
        }
      }
    }
  }
  Match(TokenKind::kRParen);
  if (member && !array_name.empty()) {
    ConstraintForeachRef ref;
    ref.array_name = array_name;
    ref.loop_var_count = loop_var_count;
    ref.loc = foreach_loc;
    member->constraint_foreach_refs.push_back(ref);
  }
}

void Parser::CheckConstraintExprToken(const Token& tok) {
  switch (tok.kind) {
    case TokenKind::kEqEqEq:
    case TokenKind::kBangEqEq:
      // 18.3: 4-state operators are illegal in a constraint.
      diag_.Error(tok.loc,
                  "4-state equality operator is not allowed in a constraint");
      break;
    case TokenKind::kPlusPlus:
    case TokenKind::kMinusMinus:
      // 18.5: operators with side effects are not allowed in a constraint.
      diag_.Error(tok.loc,
                  "operator with side effects is not allowed in a constraint");
      break;
    case TokenKind::kIntLiteral:
    case TokenKind::kUnbasedUnsizedLiteral:
      // 18.3: 4-state values (x or z) are illegal in a constraint.
      if (LiteralHasFourStateDigit(tok.text)) {
        diag_.Error(tok.loc,
                    "4-state value is not allowed in a constraint");
      }
      break;
    default:
      break;
  }
}

}
