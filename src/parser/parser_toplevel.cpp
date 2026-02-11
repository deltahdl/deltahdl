#include "parser/parser.h"

namespace delta {

// --- Gate primitive parsing ---

// clang-format off
static GateKind TokenToGateKind(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwAnd:      return GateKind::kAnd;
    case TokenKind::kKwNand:     return GateKind::kNand;
    case TokenKind::kKwOr:       return GateKind::kOr;
    case TokenKind::kKwNor:      return GateKind::kNor;
    case TokenKind::kKwXor:      return GateKind::kXor;
    case TokenKind::kKwXnor:     return GateKind::kXnor;
    case TokenKind::kKwBuf:      return GateKind::kBuf;
    case TokenKind::kKwNot:      return GateKind::kNot;
    case TokenKind::kKwBufif0:   return GateKind::kBufif0;
    case TokenKind::kKwBufif1:   return GateKind::kBufif1;
    case TokenKind::kKwNotif0:   return GateKind::kNotif0;
    case TokenKind::kKwNotif1:   return GateKind::kNotif1;
    case TokenKind::kKwTran:     return GateKind::kTran;
    case TokenKind::kKwRtran:    return GateKind::kRtran;
    case TokenKind::kKwTranif0:  return GateKind::kTranif0;
    case TokenKind::kKwTranif1:  return GateKind::kTranif1;
    case TokenKind::kKwRtranif0: return GateKind::kRtranif0;
    case TokenKind::kKwRtranif1: return GateKind::kRtranif1;
    case TokenKind::kKwNmos:     return GateKind::kNmos;
    case TokenKind::kKwPmos:     return GateKind::kPmos;
    case TokenKind::kKwRnmos:    return GateKind::kRnmos;
    case TokenKind::kKwRpmos:    return GateKind::kRpmos;
    case TokenKind::kKwCmos:     return GateKind::kCmos;
    case TokenKind::kKwRcmos:    return GateKind::kRcmos;
    case TokenKind::kKwPullup:   return GateKind::kPullup;
    case TokenKind::kKwPulldown: return GateKind::kPulldown;
    default:                     return GateKind::kAnd;
  }
}
// clang-format on

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

// clang-format off
uint8_t Parser::ParseStrength0() {
  auto k = Consume().kind;
  switch (k) {
    case TokenKind::kKwHighz0:  return 1;
    case TokenKind::kKwWeak0:   return 2;
    case TokenKind::kKwPull0:   return 3;
    case TokenKind::kKwStrong0: return 4;
    case TokenKind::kKwSupply0: return 5;
    default:                    return 0;
  }
}

uint8_t Parser::ParseStrength1() {
  auto k = Consume().kind;
  switch (k) {
    case TokenKind::kKwHighz1:  return 1;
    case TokenKind::kKwWeak1:   return 2;
    case TokenKind::kKwPull1:   return 3;
    case TokenKind::kKwStrong1: return 4;
    case TokenKind::kKwSupply1: return 5;
    default:                    return 0;
  }
}
// clang-format on

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
    Expect(TokenKind::kKwInput);
    udp->input_names.push_back(Expect(TokenKind::kIdentifier).text);
  }
  Expect(TokenKind::kRParen);
  Expect(TokenKind::kSemicolon);

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
  while (!Check(TokenKind::kKwEndinterface) && !AtEnd()) {
    if (Check(TokenKind::kKwModport)) {
      ParseModportDecl(decl->modports);
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
  // clang-format off
  if      (Check(TokenKind::kKwInput))  { cur_dir = Direction::kInput;  Consume(); }
  else if (Check(TokenKind::kKwOutput)) { cur_dir = Direction::kOutput; Consume(); }
  else if (Check(TokenKind::kKwInout))  { cur_dir = Direction::kInout;  Consume(); }
  else if (Check(TokenKind::kKwRef))    { cur_dir = Direction::kRef;    Consume(); }
  // clang-format on

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
  while (!Check(TokenKind::kKwEndprogram) && !AtEnd()) {
    ParseModuleItem(decl->items);
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
    // Skip parameter value assignment: #(expr, ...)
    if (Check(TokenKind::kHash)) {
      Consume();
      std::vector<Expr*> discard;
      ParseParenList(discard);
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
  Match(TokenKind::kKwInterface);
  Expect(TokenKind::kKwClass);
  Match(TokenKind::kKwAutomatic);
  Match(TokenKind::kKwStatic);
  decl->name = Expect(TokenKind::kIdentifier).text;
  known_types_.insert(decl->name);

  // Optional parameter port list: #(parameter ...) (§8.25)
  if (Check(TokenKind::kHash)) {
    Consume();
    Expect(TokenKind::kLParen);
    if (!Check(TokenKind::kRParen)) {
      ParseParamPortDecl(decl->params);
      while (Match(TokenKind::kComma)) {
        ParseParamPortDecl(decl->params);
      }
    }
    Expect(TokenKind::kRParen);
  }

  if (Match(TokenKind::kKwExtends)) ParseClassExtendsClause(decl);
  // §8.26: 'implements' with optional #(...) parameter assignments
  if (Match(TokenKind::kKwImplements)) ParseClassExtendsClause(decl);
  Expect(TokenKind::kSemicolon);

  while (!Check(TokenKind::kKwEndclass) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    decl->members.push_back(ParseClassMember());
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
    // clang-format off
    if      (Match(TokenKind::kKwLocal))     { m->is_local = true; }
    else if (Match(TokenKind::kKwProtected)) { m->is_protected = true; }
    else if (Match(TokenKind::kKwStatic))    { m->is_static = true; }
    else if (Match(TokenKind::kKwVirtual))   { m->is_virtual = true; }
    else if (Match(TokenKind::kKwPure))      { m->is_virtual = true; proto = true; }
    else if (Match(TokenKind::kKwRand))      { m->is_rand = true; }
    else if (Match(TokenKind::kKwRandc))     { m->is_randc = true; }
    else if (Match(TokenKind::kKwExtern))    { proto = true; }
    else { break; }
    // clang-format on
  }
  return proto;
}

ClassMember* Parser::ParseClassMember() {
  auto* member = arena_.Create<ClassMember>();
  member->loc = CurrentLoc();
  bool proto = ParseClassQualifiers(member);

  if (Check(TokenKind::kKwFunction)) {
    member->kind = ClassMemberKind::kMethod;
    member->method = ParseFunctionDecl(proto);
    return member;
  }
  if (Check(TokenKind::kKwTask)) {
    member->kind = ClassMemberKind::kMethod;
    member->method = ParseTaskDecl(proto);
    return member;
  }
  if (Check(TokenKind::kKwConstraint)) return ParseConstraintStub(member);
  // §8.5 typedef inside class body (enum, struct, etc.)
  if (Check(TokenKind::kKwTypedef)) {
    member->kind = ClassMemberKind::kProperty;
    member->name = ParseTypedef()->name;
    return member;
  }
  // §8.5 parameter/localparam inside class body
  if (Check(TokenKind::kKwParameter)) {
    member->kind = ClassMemberKind::kProperty;
    member->name = ParseParamDecl()->name;
    return member;
  }
  if (Check(TokenKind::kKwLocalparam)) {
    member->kind = ClassMemberKind::kProperty;
    member->name = ParseParamDecl()->name;
    return member;
  }

  // Property: type name [= expr] ;
  member->kind = ClassMemberKind::kProperty;
  member->data_type = ParseDataType();
  member->name = Expect(TokenKind::kIdentifier).text;
  if (Match(TokenKind::kEq)) member->init_expr = ParseExpr();
  Expect(TokenKind::kSemicolon);
  return member;
}

ClassMember* Parser::ParseConstraintStub(ClassMember* member) {
  member->kind = ClassMemberKind::kConstraint;
  Consume();  // constraint keyword
  member->name = Expect(TokenKind::kIdentifier).text;
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
