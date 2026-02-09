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

ModuleItem* Parser::ParseGateInst() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kGateInst;
  item->loc = CurrentLoc();
  item->gate_kind = TokenToGateKind(CurrentToken().kind);
  Consume();  // gate keyword

  // Optional delay: #(expr) or #number.
  if (Check(TokenKind::kHash)) {
    Consume();
    if (Match(TokenKind::kLParen)) {
      item->gate_delay = ParseExpr();
      Expect(TokenKind::kRParen);
    } else {
      item->gate_delay = ParsePrimaryExpr();
    }
  }

  // Optional instance name (identifier not followed by nothing meaningful
  // except '(' or '[').
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
  Expect(TokenKind::kSemicolon);
  return item;
}

// --- Interface declaration ---

ModuleDecl* Parser::ParseInterfaceDecl() {
  auto* decl = arena_.Create<ModuleDecl>();
  decl->decl_kind = ModuleDeclKind::kInterface;
  decl->range.start = CurrentLoc();
  Expect(TokenKind::kKwInterface);

  decl->name = Expect(TokenKind::kIdentifier).text;
  ParseParamsPortsAndSemicolon(*decl);

  while (!Check(TokenKind::kKwEndinterface) && !AtEnd()) {
    if (Check(TokenKind::kKwModport)) {
      decl->modports.push_back(ParseModportDecl());
    } else {
      ParseModuleItem(decl->items);
    }
  }
  Expect(TokenKind::kKwEndinterface);
  decl->range.end = CurrentLoc();
  return decl;
}

// --- Modport declaration ---

ModportDecl* Parser::ParseModportDecl() {
  auto* mp = arena_.Create<ModportDecl>();
  mp->loc = CurrentLoc();
  Expect(TokenKind::kKwModport);
  mp->name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kLParen);

  Direction cur_dir = Direction::kNone;
  do {
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
    ModportPort port;
    port.direction = cur_dir;
    port.name = Expect(TokenKind::kIdentifier).text;
    mp->ports.push_back(port);
  } while (Match(TokenKind::kComma));

  Expect(TokenKind::kRParen);
  Expect(TokenKind::kSemicolon);
  return mp;
}

// --- Program declaration ---

ModuleDecl* Parser::ParseProgramDecl() {
  auto* decl = arena_.Create<ModuleDecl>();
  decl->decl_kind = ModuleDeclKind::kProgram;
  decl->range.start = CurrentLoc();
  Expect(TokenKind::kKwProgram);

  decl->name = Expect(TokenKind::kIdentifier).text;
  ParseParamsPortsAndSemicolon(*decl);

  while (!Check(TokenKind::kKwEndprogram) && !AtEnd()) {
    ParseModuleItem(decl->items);
  }
  Expect(TokenKind::kKwEndprogram);
  decl->range.end = CurrentLoc();
  return decl;
}

// --- Class declaration ---

ClassDecl* Parser::ParseClassDecl() {
  auto* decl = arena_.Create<ClassDecl>();
  decl->range.start = CurrentLoc();

  if (Match(TokenKind::kKwVirtual)) {
    decl->is_virtual = true;
  }
  Expect(TokenKind::kKwClass);
  decl->name = Expect(TokenKind::kIdentifier).text;
  known_types_.insert(decl->name);

  // Optional extends.
  if (Match(TokenKind::kKwExtends)) {
    decl->base_class = Expect(TokenKind::kIdentifier).text;
  }

  Expect(TokenKind::kSemicolon);

  while (!Check(TokenKind::kKwEndclass) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;  // skip empty items
    decl->members.push_back(ParseClassMember());
  }
  Expect(TokenKind::kKwEndclass);
  decl->range.end = CurrentLoc();
  return decl;
}

// --- Class member parsing ---

ClassMember* Parser::ParseClassMember() {
  auto* member = arena_.Create<ClassMember>();
  member->loc = CurrentLoc();

  // Parse optional qualifier chain.
  while (true) {
    // clang-format off
    if      (Match(TokenKind::kKwLocal))     { member->is_local = true; }
    else if (Match(TokenKind::kKwProtected)) { member->is_protected = true; }
    else if (Match(TokenKind::kKwStatic))    { member->is_static = true; }
    else if (Match(TokenKind::kKwVirtual))   { member->is_virtual = true; }
    else if (Match(TokenKind::kKwRand))      { member->is_rand = true; }
    else if (Match(TokenKind::kKwRandc))     { member->is_randc = true; }
    else { break; }
    // clang-format on
  }

  if (Check(TokenKind::kKwFunction)) {
    member->kind = ClassMemberKind::kMethod;
    member->method = ParseFunctionDecl();
    return member;
  }
  if (Check(TokenKind::kKwTask)) {
    member->kind = ClassMemberKind::kMethod;
    member->method = ParseTaskDecl();
    return member;
  }
  if (Check(TokenKind::kKwConstraint)) {
    return ParseConstraintStub(member);
  }

  // Property: type name [= expr] ;
  member->kind = ClassMemberKind::kProperty;
  member->data_type = ParseDataType();
  member->name = Expect(TokenKind::kIdentifier).text;
  if (Match(TokenKind::kEq)) {
    member->init_expr = ParseExpr();
  }
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
