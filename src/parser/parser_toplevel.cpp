#include "parser/parser.h"

namespace delta {

// --- Gate primitive parsing ---

static GateKind TokenToGateKind(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwAnd:
      return GateKind::kAnd;
    case TokenKind::kKwNand:
      return GateKind::kNand;
    case TokenKind::kKwOr:
      return GateKind::kOr;
    case TokenKind::kKwNor:
      return GateKind::kNor;
    case TokenKind::kKwXor:
      return GateKind::kXor;
    case TokenKind::kKwXnor:
      return GateKind::kXnor;
    case TokenKind::kKwBuf:
      return GateKind::kBuf;
    case TokenKind::kKwNot:
      return GateKind::kNot;
    case TokenKind::kKwBufif0:
      return GateKind::kBufif0;
    case TokenKind::kKwBufif1:
      return GateKind::kBufif1;
    case TokenKind::kKwNotif0:
      return GateKind::kNotif0;
    case TokenKind::kKwNotif1:
      return GateKind::kNotif1;
    case TokenKind::kKwTran:
      return GateKind::kTran;
    case TokenKind::kKwRtran:
      return GateKind::kRtran;
    case TokenKind::kKwTranif0:
      return GateKind::kTranif0;
    case TokenKind::kKwTranif1:
      return GateKind::kTranif1;
    case TokenKind::kKwRtranif0:
      return GateKind::kRtranif0;
    case TokenKind::kKwRtranif1:
      return GateKind::kRtranif1;
    case TokenKind::kKwNmos:
      return GateKind::kNmos;
    case TokenKind::kKwPmos:
      return GateKind::kPmos;
    case TokenKind::kKwRnmos:
      return GateKind::kRnmos;
    case TokenKind::kKwRpmos:
      return GateKind::kRpmos;
    case TokenKind::kKwCmos:
      return GateKind::kCmos;
    case TokenKind::kKwRcmos:
      return GateKind::kRcmos;
    case TokenKind::kKwPullup:
      return GateKind::kPullup;
    case TokenKind::kKwPulldown:
      return GateKind::kPulldown;
    default:
      return GateKind::kAnd;
  }
}

bool Parser::IsAtGateKeyword() {
  switch (CurrentToken().kind) {
    case TokenKind::kKwAnd:
    case TokenKind::kKwNand:
    case TokenKind::kKwOr:
    case TokenKind::kKwNor:
    case TokenKind::kKwXor:
    case TokenKind::kKwXnor:
    case TokenKind::kKwBuf:
    case TokenKind::kKwNot:
    case TokenKind::kKwBufif0:
    case TokenKind::kKwBufif1:
    case TokenKind::kKwNotif0:
    case TokenKind::kKwNotif1:
    case TokenKind::kKwTran:
    case TokenKind::kKwRtran:
    case TokenKind::kKwTranif0:
    case TokenKind::kKwTranif1:
    case TokenKind::kKwRtranif0:
    case TokenKind::kKwRtranif1:
    case TokenKind::kKwNmos:
    case TokenKind::kKwPmos:
    case TokenKind::kKwRnmos:
    case TokenKind::kKwRpmos:
    case TokenKind::kKwCmos:
    case TokenKind::kKwRcmos:
    case TokenKind::kKwPullup:
    case TokenKind::kKwPulldown:
      return true;
    default:
      return false;
  }
}

uint8_t Parser::ParseStrength0() {
  auto k = Consume().kind;
  switch (k) {
    case TokenKind::kKwHighz0:
      return 1;
    case TokenKind::kKwWeak0:
      return 2;
    case TokenKind::kKwPull0:
      return 3;
    case TokenKind::kKwStrong0:
      return 4;
    case TokenKind::kKwSupply0:
      return 5;
    default:
      return 0;
  }
}

uint8_t Parser::ParseStrength1() {
  auto k = Consume().kind;
  switch (k) {
    case TokenKind::kKwHighz1:
      return 1;
    case TokenKind::kKwWeak1:
      return 2;
    case TokenKind::kKwPull1:
      return 3;
    case TokenKind::kKwStrong1:
      return 4;
    case TokenKind::kKwSupply1:
      return 5;
    default:
      return 0;
  }
}

// Parse gate terminals when '(' was already consumed (no strength spec).
void Parser::ParseInlineGateTerminals(GateKind kind, SourceLoc loc,
                                      std::vector<ModuleItem*>& items) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kGateInst;
  item->loc = loc;
  item->gate_kind = kind;
  item->gate_terminals.push_back(ParseExpr());
  while (Match(TokenKind::kComma)) {
    item->gate_terminals.push_back(ParseExpr());
  }
  Expect(TokenKind::kRParen);
  items.push_back(item);
  while (Match(TokenKind::kComma)) {
    items.push_back(ParseOneGateInstance(kind, loc));
  }
  Expect(TokenKind::kSemicolon);
}

ModuleItem* Parser::ParseOneGateInstance(GateKind kind, SourceLoc loc) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kGateInst;
  item->loc = loc;
  item->gate_kind = kind;

  // Optional instance name.
  if (Check(TokenKind::kIdentifier)) {
    item->gate_inst_name = Consume().text;
  }

  // Terminal list.
  Expect(TokenKind::kLParen);
  item->gate_terminals.push_back(ParseExpr());
  while (Match(TokenKind::kComma)) {
    item->gate_terminals.push_back(ParseExpr());
  }
  Expect(TokenKind::kRParen);
  return item;
}

static bool IsStrength0Token(TokenKind k) {
  switch (k) {
    case TokenKind::kKwSupply0:
    case TokenKind::kKwStrong0:
    case TokenKind::kKwPull0:
    case TokenKind::kKwWeak0:
    case TokenKind::kKwHighz0:
      return true;
    default:
      return false;
  }
}

static bool IsStrength1Token(TokenKind k) {
  switch (k) {
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

Expr* Parser::ParseGateDelay() {
  if (!Check(TokenKind::kHash)) return nullptr;
  Consume();
  if (Match(TokenKind::kLParen)) {
    auto* e = ParseExpr();
    Expect(TokenKind::kRParen);
    return e;
  }
  return ParsePrimaryExpr();
}

void Parser::ParseGateInst(std::vector<ModuleItem*>& items) {
  auto loc = CurrentLoc();
  auto gate_kind = TokenToGateKind(CurrentToken().kind);
  Consume();  // gate keyword

  // Optional strength: (strength0, strength1) or vice versa.
  // Peek inside '(' to check for strength keywords before consuming.
  uint8_t str0 = 0;
  uint8_t str1 = 0;
  bool has_strength = false;
  if (Check(TokenKind::kLParen)) {
    Consume();  // tentatively consume '('
    auto tk = CurrentToken().kind;
    has_strength = IsStrength0Token(tk) || IsStrength1Token(tk);
    if (!has_strength) {
      // Not strength — already consumed '(', parse unnamed instance inline.
      ParseInlineGateTerminals(gate_kind, loc, items);
      return;
    }
    // Parse strength spec.
    if (IsStrength0Token(tk)) {
      str0 = ParseStrength0();
      Expect(TokenKind::kComma);
      str1 = ParseStrength1();
    } else {
      str1 = ParseStrength1();
      Expect(TokenKind::kComma);
      str0 = ParseStrength0();
    }
    Expect(TokenKind::kRParen);
  }

  Expr* delay = ParseGateDelay();

  // Parse comma-separated instances.
  auto* first = ParseOneGateInstance(gate_kind, loc);
  first->drive_strength0 = str0;
  first->drive_strength1 = str1;
  first->gate_delay = delay;
  items.push_back(first);

  while (Match(TokenKind::kComma)) {
    auto* next = ParseOneGateInstance(gate_kind, loc);
    next->drive_strength0 = str0;
    next->drive_strength1 = str1;
    next->gate_delay = delay;
    items.push_back(next);
  }
  Expect(TokenKind::kSemicolon);
}

// --- UDP declaration (§29) ---

static char UdpCharFromToken(const Token& tok) {
  if (tok.kind == TokenKind::kStar) return '*';
  if (tok.kind == TokenKind::kMinus) return '-';
  if (tok.kind == TokenKind::kQuestion) return '?';
  if (!tok.text.empty()) return tok.text[0];
  return '?';
}

UdpDecl* Parser::ParseUdpDecl() {
  auto* udp = arena_.Create<UdpDecl>();
  udp->range.start = CurrentLoc();
  Expect(TokenKind::kKwPrimitive);
  udp->name = Expect(TokenKind::kIdentifier).text;

  // Port list: (output [reg] out_name, input in1, in2, ...)
  Expect(TokenKind::kLParen);
  Expect(TokenKind::kKwOutput);
  if (Match(TokenKind::kKwReg)) {
    udp->is_sequential = true;
  }
  udp->output_name = Expect(TokenKind::kIdentifier).text;
  while (Match(TokenKind::kComma)) {
    Match(TokenKind::kKwInput);  // Optional: input keyword may appear once
    udp->input_names.push_back(Expect(TokenKind::kIdentifier).text);
  }
  Expect(TokenKind::kRParen);
  Expect(TokenKind::kSemicolon);

  // Optional initial statement for sequential UDPs (§29.7).
  if (Match(TokenKind::kKwInitial)) {
    udp->has_initial = true;
    Expect(TokenKind::kIdentifier);  // output reg name
    Expect(TokenKind::kEq);
    udp->initial_value = UdpCharFromToken(Consume());
    // Skip optional size prefix like 1'b in "1'b1".
    while (!Check(TokenKind::kSemicolon) && !AtEnd()) {
      udp->initial_value = UdpCharFromToken(Consume());
    }
    Expect(TokenKind::kSemicolon);
  }

  // Table block.
  Expect(TokenKind::kKwTable);
  while (!Check(TokenKind::kKwEndtable) && !AtEnd()) {
    UdpTableRow row;
    // Read input entries until ':'
    while (!Check(TokenKind::kColon) && !AtEnd()) {
      row.inputs.push_back(UdpCharFromToken(Consume()));
    }
    Expect(TokenKind::kColon);
    if (udp->is_sequential) {
      // Sequential: inputs : current_state : output
      row.current_state = UdpCharFromToken(Consume());
      Expect(TokenKind::kColon);
    }
    row.output = UdpCharFromToken(Consume());
    Expect(TokenKind::kSemicolon);
    udp->table.push_back(row);
  }
  Expect(TokenKind::kKwEndtable);
  Expect(TokenKind::kKwEndprimitive);
  udp->range.end = CurrentLoc();
  return udp;
}

// --- Interface declaration ---

ModuleDecl* Parser::ParseInterfaceDecl() {
  auto* decl = arena_.Create<ModuleDecl>();
  decl->decl_kind = ModuleDeclKind::kInterface;
  decl->range.start = CurrentLoc();
  Expect(TokenKind::kKwInterface);

  // Optional lifetime qualifier (§3.4)
  Match(TokenKind::kKwAutomatic) || Match(TokenKind::kKwStatic);

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
  if (Match(TokenKind::kColon)) ExpectIdentifier();
  decl->range.end = CurrentLoc();
  return decl;
}

// --- Modport declaration ---

ModportPort Parser::ParseModportPort(Direction& cur_dir) {
  ModportPort port;
  // import/export task/function names (§25.7)
  if (Check(TokenKind::kKwImport)) {
    Consume();
    port.is_import = true;
    port.name = Expect(TokenKind::kIdentifier).text;
    return port;
  }
  if (Check(TokenKind::kKwExport)) {
    Consume();
    port.is_export = true;
    port.name = Expect(TokenKind::kIdentifier).text;
    return port;
  }
  // Direction keywords
  if (Check(TokenKind::kKwInput)) {
    cur_dir = Direction::kInput;
    Consume();
  } else if (Check(TokenKind::kKwOutput)) {
    cur_dir = Direction::kOutput;
    Consume();
  } else if (Check(TokenKind::kKwInout)) {
    cur_dir = Direction::kInout;
    Consume();
  } else if (Check(TokenKind::kKwRef)) {
    cur_dir = Direction::kRef;
    Consume();
  }

  // Port expression syntax: .name(expr) (§25.5.4)
  if (Match(TokenKind::kDot)) {
    port.name = Expect(TokenKind::kIdentifier).text;
    Expect(TokenKind::kLParen);
    port.expr = ParseExpr();
    Expect(TokenKind::kRParen);
    return port;
  }
  port.direction = cur_dir;
  port.name = Expect(TokenKind::kIdentifier).text;
  return port;
}

void Parser::ParseModportDecl(std::vector<ModportDecl*>& out) {
  Expect(TokenKind::kKwModport);
  do {
    auto* mp = arena_.Create<ModportDecl>();
    mp->loc = CurrentLoc();
    mp->name = Expect(TokenKind::kIdentifier).text;
    Expect(TokenKind::kLParen);
    Direction cur_dir = Direction::kNone;
    do {
      mp->ports.push_back(ParseModportPort(cur_dir));
    } while (Match(TokenKind::kComma));
    Expect(TokenKind::kRParen);
    out.push_back(mp);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
}

// --- Program declaration ---

ModuleDecl* Parser::ParseProgramDecl() {
  auto* decl = arena_.Create<ModuleDecl>();
  decl->decl_kind = ModuleDeclKind::kProgram;
  decl->range.start = CurrentLoc();
  Expect(TokenKind::kKwProgram);

  // Optional lifetime qualifier (§3.4)
  Match(TokenKind::kKwAutomatic) || Match(TokenKind::kKwStatic);

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
  if (Match(TokenKind::kColon)) ExpectIdentifier();
  decl->range.end = CurrentLoc();
  return decl;
}

// --- Class declaration ---

void Parser::ParseClassExtendsClause(ClassDecl* decl) {
  // §8.26: interface classes may extend multiple base classes
  // (comma-separated).
  do {
    auto name = Expect(TokenKind::kIdentifier).text;
    while (Match(TokenKind::kColonColon)) {
      name = Expect(TokenKind::kIdentifier).text;
    }
    if (decl->base_class.empty()) decl->base_class = name;
    // Skip parameter value assignment: #(type_or_expr, ...)
    if (Check(TokenKind::kHash)) {
      Consume();
      ParseTypeParamList();
    }
    // Skip constructor arguments: (expr, ...)
    if (Check(TokenKind::kLParen)) {
      std::vector<Expr*> discard;
      ParseParenList(discard);
    }
  } while (Match(TokenKind::kComma));
}

ClassDecl* Parser::ParseClassDecl() {
  auto* decl = arena_.Create<ClassDecl>();
  decl->range.start = CurrentLoc();
  decl->is_virtual = Match(TokenKind::kKwVirtual);
  decl->is_interface = Match(TokenKind::kKwInterface);
  Expect(TokenKind::kKwClass);
  // final_specifier ::= : final (A.1.2 / §8.20)
  if (Match(TokenKind::kColon)) {
    Expect(TokenKind::kKwFinal);
    decl->is_final = true;
  }
  Match(TokenKind::kKwAutomatic);
  Match(TokenKind::kKwStatic);
  decl->name = Expect(TokenKind::kIdentifier).text;
  known_types_.insert(decl->name);

  // Optional parameter port list: #(parameter ...) (§8.25)
  if (Check(TokenKind::kHash)) {
    Consume();
    Expect(TokenKind::kLParen);
    while (!Check(TokenKind::kRParen) && !AtEnd()) {
      ParseParamPortDecl(decl->params);
      Match(TokenKind::kComma);
    }
    Expect(TokenKind::kRParen);
  }

  if (Match(TokenKind::kKwExtends)) ParseClassExtendsClause(decl);
  // §8.26: 'implements' with optional #(...) parameter assignments
  if (Match(TokenKind::kKwImplements)) ParseClassExtendsClause(decl);
  Expect(TokenKind::kSemicolon);

  while (!Check(TokenKind::kKwEndclass) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    auto before = lexer_.SavePos().pos;
    ParseClassMembers(decl->members);
    // Safety: if no progress was made, skip a token to avoid infinite loops.
    if (lexer_.SavePos().pos == before) Consume();
  }
  Expect(TokenKind::kKwEndclass);
  if (Match(TokenKind::kColon)) ExpectIdentifier();
  decl->range.end = CurrentLoc();
  return decl;
}

// --- Class member qualifier parsing ---

bool Parser::ParseClassQualifiers(ClassMember* m) {
  bool proto = false;
  while (true) {
    if (Match(TokenKind::kKwLocal)) {
      m->is_local = true;
    } else if (Match(TokenKind::kKwProtected)) {
      m->is_protected = true;
    } else if (Match(TokenKind::kKwStatic)) {
      m->is_static = true;
    } else if (Match(TokenKind::kKwVirtual)) {
      m->is_virtual = true;
    } else if (Match(TokenKind::kKwPure)) {
      m->is_virtual = true;
      proto = true;
    } else if (Match(TokenKind::kKwRand)) {
      m->is_rand = true;
    } else if (Match(TokenKind::kKwRandc)) {
      m->is_randc = true;
    } else if (Match(TokenKind::kKwConst)) {
      m->is_const = true;
    } else if (Match(TokenKind::kKwExtern)) {
      proto = true;
    } else {
      break;
    }
  }
  return proto;
}

void Parser::ParseClassMembers(std::vector<ClassMember*>& members) {
  auto* member = arena_.Create<ClassMember>();
  member->loc = CurrentLoc();
  bool proto = ParseClassQualifiers(member);

  if (Check(TokenKind::kKwFunction)) {
    member->kind = ClassMemberKind::kMethod;
    member->method = ParseFunctionDecl(proto);
    // §13.8: Propagate static qualifier to the method's ModuleItem.
    if (member->is_static) member->method->is_static = true;
    members.push_back(member);
    return;
  }
  if (Check(TokenKind::kKwTask)) {
    member->kind = ClassMemberKind::kMethod;
    member->method = ParseTaskDecl(proto);
    if (member->is_static) member->method->is_static = true;
    members.push_back(member);
    return;
  }
  if (Check(TokenKind::kKwConstraint)) {
    members.push_back(ParseConstraintStub(member));
    return;
  }
  if (Check(TokenKind::kKwTypedef)) {
    member->kind = ClassMemberKind::kTypedef;
    member->typedef_item = ParseTypedef();
    member->name = member->typedef_item->name;
    members.push_back(member);
    return;
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
    return;
  }
  // class_item: class_declaration | interface_class_declaration (A.1.9)
  if (IsAtClassDecl()) {
    member->kind = ClassMemberKind::kClassDecl;
    member->nested_class = ParseClassDecl();
    member->name = member->nested_class->name;
    members.push_back(member);
    return;
  }
  // class_item: covergroup_declaration (A.1.9)
  if (Check(TokenKind::kKwCovergroup)) {
    member->kind = ClassMemberKind::kCovergroup;
    std::vector<ModuleItem*> temp;
    ParseCovergroupDecl(temp);
    if (!temp.empty()) member->name = temp[0]->name;
    members.push_back(member);
    return;
  }

  // Property: type name [= expr] {, name [= expr]} ;
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
  Consume();  // constraint keyword
  // Optional dynamic_override_specifiers: [:initial|:extends] [:final]
  if (Match(TokenKind::kColon)) {
    Match(TokenKind::kKwInitial) || Match(TokenKind::kKwExtends) ||
        Match(TokenKind::kKwFinal);
  }
  if (Match(TokenKind::kColon)) Match(TokenKind::kKwFinal);
  member->name = Expect(TokenKind::kIdentifier).text;
  // §18.5.1: extern/implicit constraint declaration — no body
  if (Match(TokenKind::kSemicolon)) return member;
  Expect(TokenKind::kLBrace);
  int depth = 1;
  while (depth > 0 && !AtEnd()) {
    if (Match(TokenKind::kLBrace)) {
      ++depth;
    } else if (Match(TokenKind::kRBrace)) {
      --depth;
    } else {
      Consume();
    }
  }
  return member;
}

}  // namespace delta
