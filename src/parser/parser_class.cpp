#include "parser/parser.h"

namespace delta {

// CPD-dedup: an interface declaration and a program declaration are written
// the same way apart from their keywords and their bodies, so the head and the
// tail either one reads are parsed in one place here.
struct ParserClassHelpers {
  // The keyword, the optional lifetime, the name, and the parameter and port
  // lists. Returns true when the ports were written in the non-ANSI style, in
  // which case the body still has their directions to read. The subclause is
  // the caller's, since the two declarations this reads are stated in different
  // places: §25.3 gives the interface syntax and §24.3 the program construct.
  static bool ParseHead(Parser& p, ModuleDecl* decl, TokenKind keyword,
                        Subclause subclause) {
    p.Expect(keyword, subclause);

    decl->is_automatic = p.Match(TokenKind::kKwAutomatic);
    if (!decl->is_automatic) p.Match(TokenKind::kKwStatic);

    decl->name = p.Expect(TokenKind::kIdentifier, subclause).text;
    p.ParseParamsPortsAndSemicolon(*decl);
    return !decl->ports.empty() && decl->ports[0].direction == Direction::kNone;
  }

  // The end keyword, the optional label repeating the name, and the end of the
  // declaration's source range. The subclause is the caller's, for the reason
  // given on ParseHead.
  static void ParseTail(Parser& p, ModuleDecl* decl, TokenKind end_keyword,
                        Subclause subclause) {
    p.Expect(end_keyword, subclause);
    p.MatchEndLabel(decl->name);
    decl->range.end = p.CurrentLoc();
  }
};

ModuleDecl* Parser::ParseInterfaceDecl() {
  auto* decl = arena_.Create<ModuleDecl>();
  decl->decl_kind = ModuleDeclKind::kInterface;
  decl->range.start = CurrentLoc();
  bool non_ansi = ParserClassHelpers::ParseHead(
      *this, decl, TokenKind::kKwInterface, Subclause("25.3"));

  auto* prev_module = current_module_;
  current_module_ = decl;
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
  ParserClassHelpers::ParseTail(*this, decl, TokenKind::kKwEndinterface,
                                Subclause("25.3"));
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
    item->name = Expect(TokenKind::kIdentifier, Subclause("25.5")).text;
    if (Check(TokenKind::kLParen)) item->func_args = ParseFunctionArgs(false);
    port.prototype = item;
    port.name = item->name;
  } else if (Check(TokenKind::kKwFunction)) {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kFunctionDecl;
    item->loc = CurrentLoc();
    Consume();
    item->data_type = ParseFunctionReturnType();
    item->name = Expect(TokenKind::kIdentifier, Subclause("25.5")).text;
    if (Check(TokenKind::kLParen)) item->func_args = ParseFunctionArgs(false);
    port.prototype = item;
    port.name = item->name;
  } else {
    port.name = Expect(TokenKind::kIdentifier, Subclause("25.5")).text;
  }
  return port;
}

ModportPort Parser::ParseModportSimplePort(Direction dir) {
  ModportPort port;
  port.direction = dir;
  if (Match(TokenKind::kDot)) {
    port.is_named_port = true;
    port.name = Expect(TokenKind::kIdentifier, Subclause("25.5.4")).text;
    Expect(TokenKind::kLParen, Subclause("25.5.4"));
    if (!Check(TokenKind::kRParen)) port.expr = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("25.5.4"));
  } else {
    port.name = Expect(TokenKind::kIdentifier, Subclause("25.5")).text;
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

void Parser::ParseModportPortEntry(ModportDecl* mp, Direction& cur_dir,
                                   int& tf_mode) {
  ParseAttributes();
  if (Check(TokenKind::kKwClocking)) {
    tf_mode = 0;
    Consume();
    ModportPort port;
    port.is_clocking = true;
    port.name = Expect(TokenKind::kIdentifier, Subclause("25.5.5")).text;
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
}

void Parser::ParseModportItem(ModportDecl* mp) {
  Direction cur_dir = Direction::kNone;
  int tf_mode = 0;
  while (!Check(TokenKind::kRParen) && !AtEnd()) {
    auto before = lexer_.SavePos().pos;
    ParseModportPortEntry(mp, cur_dir, tf_mode);
    if (!Check(TokenKind::kRParen))
      Expect(TokenKind::kComma, Subclause("25.5"));
    // Missing ')': a token that is neither a port nor a comma (e.g. the
    // terminating ';') leaves the cursor unmoved. Stop so the caller's
    // Expect(kRParen) reports the error instead of spinning.
    if (lexer_.SavePos().pos == before) break;
  }
}

void Parser::ParseModportDecl(std::vector<ModportDecl*>& out) {
  Expect(TokenKind::kKwModport, Subclause("25.5"));
  do {
    auto* mp = arena_.Create<ModportDecl>();
    mp->loc = CurrentLoc();
    mp->name = Expect(TokenKind::kIdentifier, Subclause("25.5")).text;
    Expect(TokenKind::kLParen, Subclause("25.5"));
    ParseModportItem(mp);
    Expect(TokenKind::kRParen, Subclause("25.5"));
    out.push_back(mp);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon, Subclause("25.5"));
}

ModuleDecl* Parser::ParseProgramDecl() {
  auto* decl = arena_.Create<ModuleDecl>();
  decl->decl_kind = ModuleDeclKind::kProgram;
  decl->range.start = CurrentLoc();
  bool non_ansi = ParserClassHelpers::ParseHead(
      *this, decl, TokenKind::kKwProgram, Subclause("24.3"));

  auto* prev_module = current_module_;
  current_module_ = decl;
  while (!Check(TokenKind::kKwEndprogram) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    if (non_ansi && IsPortDirection(CurrentToken().kind)) {
      ParseNonAnsiPortDecls(*decl);
    } else {
      ParseModuleItem(decl->items);
    }
  }
  current_module_ = prev_module;
  ParserClassHelpers::ParseTail(*this, decl, TokenKind::kKwEndprogram,
                                Subclause("24.3"));
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
  Expect(TokenKind::kRParen, Subclause("8.17"));
}

namespace {

// Record one base named in a class's extends/implements clause onto decl. The
// first non-implements base becomes the class's primary base_class (and carries
// its type parameters into base_class_type_params when has_type_params is set);
// every other entry is collected as an implemented interface or an additional
// extended interface. has_type_params distinguishes 'base #(...)' from a bare
// 'base' so the no-parameter case leaves base_class_type_params untouched.
// Returns whether this base was the primary base, so the caller can route its
// following '(...)' argument list correctly.
bool RecordClassExtendsBase(ClassDecl* decl, std::string_view name,
                            std::vector<DataType> tparams, bool is_implements,
                            bool has_type_params) {
  bool is_first_base = !is_implements && decl->base_class.empty();
  if (is_first_base) {
    decl->base_class = name;
  }
  if (has_type_params && is_first_base) {
    decl->base_class_type_params = tparams;
  }
  if (is_implements) {
    decl->implements_types.push_back({name, std::move(tparams)});
  } else if (!is_first_base) {
    decl->extends_interfaces.push_back({name, std::move(tparams)});
  }
  return is_first_base;
}

}  // namespace

void Parser::ParseClassExtendsClause(ClassDecl* decl, bool is_implements) {
  // §8.13 states the extends clause and §8.26.2 the implements clause, so which
  // rule a malformed base name breaches depends on which clause is being read.
  Subclause subclause(is_implements ? "8.26.2" : "8.13");
  do {
    auto name = Expect(TokenKind::kIdentifier, subclause).text;
    while (Match(TokenKind::kColonColon)) {
      name = Expect(TokenKind::kIdentifier, subclause).text;
    }
    std::vector<DataType> tparams;
    bool has_type_params = Check(TokenKind::kHash);
    if (has_type_params) {
      Consume();
      tparams = ParseTypeParamList();
    }
    RecordClassExtendsBase(decl, name, std::move(tparams), is_implements,
                           has_type_params);

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
  Expect(TokenKind::kKwClass, Subclause("8.3"));

  if (Match(TokenKind::kColon)) {
    Expect(TokenKind::kKwFinal, Subclause("8.13"));
    decl->is_final = true;
  }
  Match(TokenKind::kKwAutomatic);
  Match(TokenKind::kKwStatic);
  decl->name = Expect(TokenKind::kIdentifier, Subclause("8.3")).text;
  known_types_.insert(decl->name);

  if (Check(TokenKind::kHash)) {
    Consume();
    Expect(TokenKind::kLParen, Subclause("8.25"));
    bool is_lp_group = false;
    while (!Check(TokenKind::kRParen) && !AtEnd()) {
      ParseParamPortDecl(decl->params, decl->type_param_names,
                         decl->localparam_port_names, is_lp_group);
      Match(TokenKind::kComma);
    }
    Expect(TokenKind::kRParen, Subclause("8.25"));
  }

  if (Match(TokenKind::kKwExtends)) ParseClassExtendsClause(decl, false);

  if (Match(TokenKind::kKwImplements)) ParseClassExtendsClause(decl, true);
  Expect(TokenKind::kSemicolon, Subclause("8.3"));

  ++class_body_depth_;
  while (!Check(TokenKind::kKwEndclass) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    auto before = lexer_.SavePos().pos;
    ParseClassMembers(decl->members);

    if (lexer_.SavePos().pos == before) Consume();
  }
  --class_body_depth_;
  Expect(TokenKind::kKwEndclass, Subclause("8.3"));
  MatchEndLabel(decl->name);
  decl->range.end = CurrentLoc();
  return decl;
}

bool Parser::TryConsumeClassQualifier(ClassMember* m, TokenKind kw,
                                      bool ClassMember::* flag,
                                      const char* dup_msg) {
  if (!Check(kw)) return false;
  if (m->*flag) diag_.Error(CurrentLoc(), dup_msg, Subclause("8.3"));
  m->*flag = true;
  Consume();
  return true;
}

bool Parser::TryConsumeAccessQualifier(ClassMember* m) {
  if (Check(TokenKind::kKwLocal)) {
    if (m->is_protected)
      diag_.Error(CurrentLoc(),
                  "cannot combine 'local' and 'protected' qualifiers",
                  Subclause("8.3"));
    if (m->is_local)
      diag_.Error(CurrentLoc(), "duplicate 'local' qualifier",
                  Subclause("8.3"));
    m->is_local = true;
    Consume();
    return true;
  }
  if (Check(TokenKind::kKwProtected)) {
    if (m->is_local)
      diag_.Error(CurrentLoc(),
                  "cannot combine 'local' and 'protected' qualifiers",
                  Subclause("8.3"));
    if (m->is_protected)
      diag_.Error(CurrentLoc(), "duplicate 'protected' qualifier",
                  Subclause("8.3"));
    m->is_protected = true;
    Consume();
    return true;
  }
  return false;
}

bool Parser::TryConsumeRandQualifier(ClassMember* m) {
  if (Check(TokenKind::kKwRand)) {
    if (m->is_randc)
      diag_.Error(CurrentLoc(), "cannot combine 'rand' and 'randc' qualifiers",
                  Subclause("8.3"));
    if (m->is_rand)
      diag_.Error(CurrentLoc(), "duplicate 'rand' qualifier", Subclause("8.3"));
    m->is_rand = true;
    Consume();
    return true;
  }
  if (Check(TokenKind::kKwRandc)) {
    if (m->is_rand)
      diag_.Error(CurrentLoc(), "cannot combine 'rand' and 'randc' qualifiers",
                  Subclause("8.3"));
    if (m->is_randc)
      diag_.Error(CurrentLoc(), "duplicate 'randc' qualifier",
                  Subclause("8.3"));
    m->is_randc = true;
    Consume();
    return true;
  }
  return false;
}

// §25.9: 'virtual' is overloaded inside a class body. It begins a virtual
// interface property type only when followed by an interface name ('virtual Bus
// b;') or the explicit 'interface' keyword ('virtual interface Bus b;'); that
// case must be left for ParseDataType. In every other position it is a member
// qualifier (virtual function/task, a nested virtual class, or ahead of further
// method qualifiers such as 'pure virtual protected function'). Peeks one token
// past 'virtual'.
bool Parser::VirtualIsClassQualifier() {
  auto saved = lexer_.SavePos();
  Consume();
  bool is_interface_type =
      Check(TokenKind::kIdentifier) || Check(TokenKind::kKwInterface);
  lexer_.RestorePos(saved);
  return !is_interface_type;
}

bool Parser::TryConsumeVirtualQualifier(ClassMember* m) {
  if (!Check(TokenKind::kKwVirtual) || !VirtualIsClassQualifier()) return false;
  if (m->is_virtual)
    diag_.Error(CurrentLoc(), "duplicate 'virtual' qualifier",
                Subclause("8.3"));
  m->is_virtual = true;
  Consume();
  return true;
}

bool Parser::ParseClassQualifiers(ClassMember* m) {
  bool proto = false;
  while (true) {
    if (TryConsumeAccessQualifier(m)) continue;
    if (TryConsumeClassQualifier(m, TokenKind::kKwStatic,
                                 &ClassMember::is_static,
                                 "duplicate 'static' qualifier"))
      continue;
    if (TryConsumeVirtualQualifier(m)) continue;
    if (Match(TokenKind::kKwPure)) {
      m->is_pure_virtual = true;
      proto = true;
      continue;
    }
    if (TryConsumeRandQualifier(m)) continue;
    if (TryConsumeClassQualifier(m, TokenKind::kKwConst, &ClassMember::is_const,
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
                "class method shall not have static lifetime",
                Subclause("8.6"));
  }

  if (member->is_static && member->is_virtual &&
      member->method->name != "new") {
    diag_.Error(member->method->loc,
                "static method shall not be declared virtual",
                Subclause("8.10"));
  }
  if (member->is_static) member->method->is_static = true;
}

void Parser::ValidateConstructorQualifiers(ClassMember* member) {
  if (member->method->name != "new") return;
  if (member->is_static) {
    diag_.Error(member->method->loc, "constructor shall not be declared static",
                Subclause("8.7"));
  }
  if (member->is_virtual) {
    diag_.Error(member->method->loc,
                "constructor shall not be declared virtual", Subclause("8.7"));
  }
}

bool Parser::TryParseMethodOrConstraint(std::vector<ClassMember*>& members,
                                        ClassMember* member, bool proto) {
  bool is_func = Check(TokenKind::kKwFunction);
  if (is_func || Check(TokenKind::kKwTask)) {
    member->kind = ClassMemberKind::kMethod;
    member->method = is_func ? ParseFunctionDecl(proto) : ParseTaskDecl(proto);
    // Mirror the method name onto the ClassMember, like every other member kind
    // (typedef/property/nested class); the name itself lives on member->method.
    member->name = member->method->name;
    ValidateClassMethod(member);
    if (is_func) ValidateConstructorQualifiers(member);
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
      m->is_param = true;
      m->name = param_items[i]->name;
      // §6.20/§8.25: carry the parameter's type and default value so the
      // lowerer can evaluate it into the class type's static-property store
      // (a class parameter is a compile-time constant of the class).
      m->data_type = param_items[i]->data_type;
      m->init_expr = param_items[i]->init_expr;
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
                "package import declaration is not allowed in class scope",
                Subclause("26.3"));
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
                "class member functions cannot be exported",
                Subclause("35.7"));
    while (!Check(TokenKind::kSemicolon) && !AtEnd()) Consume();
    Match(TokenKind::kSemicolon);
    return;
  }
  // §14.7: a class is none of the four scopes a clocking block may be declared
  // in, so one written as a class member is rejected here rather than falling
  // through to the class property form, which would ask for a property name.
  if (AtClockingDecl()) {
    RejectClockingDecl(
        "a clocking block shall not be declared inside a class; it can only be "
        "declared inside a module, interface, checker, or program");
    return;
  }
  auto* member = arena_.Create<ClassMember>();
  member->loc = CurrentLoc();
  bool proto = ParseClassQualifiers(member);

  if (TryParseKeywordClassMember(members, member, proto)) return;

  // (6.19/7.2) a class property may use an inline enum/struct/union data type,
  // which ParseDataType() does not consume; dispatch those here first, as every
  // other data-type caller must.
  DataType dtype;
  if (!TryParseInlineAggregateType(dtype)) dtype = ParseDataType();
  member->kind = ClassMemberKind::kProperty;
  member->data_type = dtype;
  member->name = Expect(TokenKind::kIdentifier, Subclause("8.5")).text;
  ParseUnpackedDims(member->unpacked_dims);
  if (Match(TokenKind::kEq)) member->init_expr = ParseExpr();
  members.push_back(member);
  ParseExtraPropertyDecls(members, member, dtype);
  Expect(TokenKind::kSemicolon, Subclause("8.5"));
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
    extra->name = Expect(TokenKind::kIdentifier, Subclause("8.5")).text;
    ParseUnpackedDims(extra->unpacked_dims);
    if (Match(TokenKind::kEq)) extra->init_expr = ParseExpr();
    members.push_back(extra);
  }
}

namespace {

// 18.5.11/18.5.13.1: the lexical context surrounding the leaf token just
// consumed in a constraint block body. prev_was_qualifier records whether the
// preceding token was a '.'/'::' (so a member/scope-qualified name is not taken
// for an unqualified call); next_is_lparen/next_is_dot/next_is_coloncolon are
// the one-token lookahead that distinguishes a call ('identifier (') from a
// continued qualified reference. All four are computed by the caller so the
// recording stays a pure operation on the member.
struct ConstraintTokenContext {
  bool prev_was_qualifier;
  bool next_is_lparen;
  bool next_is_dot;
  bool next_is_coloncolon;
};

// 18.5.11/18.5.13.1: from the leaf identifier token just consumed inside a
// constraint block body, record an unqualified function call (the 'identifier (
// ' form) and, while scanning a soft constraint, a bare local variable
// reference. in_soft is cleared when the soft constraint's expression
// terminates at its ';'.
void RecordConstraintTokenRefs(ClassMember* member, const Token& tok,
                               const ConstraintTokenContext& ctx,
                               bool& in_soft) {
  if (tok.kind == TokenKind::kIdentifier && !ctx.prev_was_qualifier &&
      ctx.next_is_lparen) {
    ConstraintFunctionCallRef ref;
    ref.callee = tok.text;
    ref.loc = tok.loc;
    if (member) member->constraint_function_call_refs.push_back(ref);
  }
  if (in_soft && tok.kind == TokenKind::kIdentifier &&
      !ctx.prev_was_qualifier && !ctx.next_is_lparen && !ctx.next_is_dot &&
      !ctx.next_is_coloncolon) {
    if (member) {
      ConstraintSoftVarRef sref;
      sref.name = tok.text;
      sref.loc = tok.loc;
      member->constraint_soft_refs.push_back(sref);
    }
  }
  // The soft constraint's expression ends at its ';'.
  if (tok.kind == TokenKind::kSemicolon) in_soft = false;
}

// 18.5.3/18.5.7.1/18.5.11/18.5.13.1: the structural tokens that the constraint
// block scan tracks for their own sake rather than as expression leaves: a
// brace adjusts the block-nesting depth, and 'soft' opens a soft-constraint
// expression whose bare local variables are collected until its ';'. The token
// has just been consumed by the caller, so this only applies its pure effect on
// the running depth/in_soft scan state.
void ApplyConstraintStructuralToken(TokenKind kind, int& depth, bool& in_soft) {
  switch (kind) {
    case TokenKind::kLBrace:
      ++depth;
      break;
    case TokenKind::kRBrace:
      --depth;
      break;
    case TokenKind::kKwSoft:
      in_soft = true;
      break;
    default:
      break;
  }
}

// 18.5.11: a leaf token closes a member/scope qualifier when it is a '.' or
// '::', so the identifier that follows is part of a qualified name rather than
// an unqualified call on the enclosing class.
bool LeafClosesQualifier(const Token& tok) {
  return tok.kind == TokenKind::kDot || tok.kind == TokenKind::kColonColon;
}

}  // namespace

// 18.5.1: parse the qualifier list ('static'/'initial'/'extends'/'final' after
// one or two ':' separators) and the constraint name. Returns true when the
// constraint is a bodyless prototype (terminated by ';'), in which case the
// caller is done; otherwise the opening '{' has been consumed.
bool Parser::ParseConstraintHeader(ClassMember* member) {
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
  member->name = Expect(TokenKind::kIdentifier, Subclause("18.5")).text;

  // 18.5.1: a constraint with no block is a prototype, completed elsewhere by
  // an external constraint block.
  if (Match(TokenKind::kSemicolon)) {
    member->is_constraint_prototype = true;
    return true;
  }
  Expect(TokenKind::kLBrace, Subclause("18.5"));
  return false;
}

// One step of the constraint-block body scan. Consumes the next structural or
// leaf token, updating depth/in_soft and recording references on member.
// carried_qualifier carries the previous leaf's '.'/'::' state; the function
// returns it updated for the next iteration.
bool Parser::ScanConstraintBodyToken(ClassMember* member, int& depth,
                                     bool& in_soft, bool carried_qualifier) {
  TokenKind kind = CurrentToken().kind;
  // 18.5.7.1: 'foreach ( array_id [ loop_variables ] )' heads an iterative
  // constraint; validate its header (the loop-variable naming rule) and
  // record it for the elaborator's dimension check before the scan resumes.
  if (kind == TokenKind::kKwForeach) {
    CheckForeachConstraintHeader(member);
    return false;
  }
  // 18.5.9: 'solve solve_before_list before solve_before_list ;' is consumed
  // through its ';', recording the two lists for the elaborator's ordering
  // and circular-dependency checks.
  if (kind == TokenKind::kKwSolve) {
    CheckSolveBeforeConstraint(member);
    return false;
  }
  // 18.5.3: 'expression dist { dist_list }' hands the brace-enclosed
  // dist_list to a dedicated scan so its default-item rules are enforced.
  if (kind == TokenKind::kKwDist) {
    Consume();
    CheckDistSet();
    // 18.5: a dist expression forms a complete expression_or_dist and may not
    // appear within another expression. Once the dist_list has been consumed,
    // the only token that may legally follow is the ';' terminating the
    // constraint_expression; an operator, ')', or any other continuation means
    // the dist was used as an operand of a surrounding expression. A bare '}'
    // (a missing terminator, or the constraint block's own close) is left to
    // the ordinary terminator handling so this rule does not fire on it.
    if (!AtEnd() && !Check(TokenKind::kSemicolon) &&
        !Check(TokenKind::kRBrace)) {
      diag_.Error(CurrentLoc(),
                  "a dist expression may not appear within another expression",
                  Subclause("18.5"));
    }
    return false;
  }
  // 18.5.13.2: 'disable soft constraint_primary ;' discards the lower-priority
  // soft constraints that reference the primary's variable. Capture the
  // variable and consume the directive up to (not including) its ';', so its
  // 'soft' keyword is not taken as opening a soft constraint and the terminator
  // still resets the relation scan as usual.
  if (kind == TokenKind::kKwDisable) {
    CaptureDisableSoftConstraint(member);
    return false;
  }
  // 18.5.13.1/structural: 'soft' opens a soft constraint and a brace adjusts
  // the block-nesting depth; consume the token and apply its pure scan effect.
  if (kind == TokenKind::kKwSoft || kind == TokenKind::kLBrace ||
      kind == TokenKind::kRBrace) {
    Consume();
    ApplyConstraintStructuralToken(kind, depth, in_soft);
    return false;
  }
  Token t = CurrentToken();
  CheckConstraintExprToken(t);
  Consume();
  // 18.5.11/18.5.13.1: with the leaf token consumed, look at the next token
  // to recognize an unqualified call ('identifier (') and a bare local
  // variable named in a soft constraint, then record them on the member.
  RecordConstraintTokenRefs(
      member, t,
      ConstraintTokenContext{carried_qualifier, Check(TokenKind::kLParen),
                             Check(TokenKind::kDot),
                             Check(TokenKind::kColonColon)},
      in_soft);
  return LeafClosesQualifier(t);
}

}  // namespace delta
