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

void Parser::ParseGateDelay(Expr*& d1, Expr*& d2, Expr*& d3) {
  if (!Check(TokenKind::kHash)) return;
  Consume();
  if (Match(TokenKind::kLParen)) {
    d1 = ParseMinTypMaxExpr();
    if (Match(TokenKind::kComma)) {
      d2 = ParseMinTypMaxExpr();
      if (Match(TokenKind::kComma)) d3 = ParseMinTypMaxExpr();
    }
    Expect(TokenKind::kRParen);
  } else if (Check(TokenKind::kIntLiteral) && CurrentToken().text == "1") {
    auto saved = lexer_.SavePos();
    auto one_tok = CurrentToken();
    Consume();
    if (Check(TokenKind::kIdentifier) && CurrentToken().text == "step") {
      Consume();
      d1 = arena_.Create<Expr>();
      d1->kind = ExprKind::kIntegerLiteral;
      d1->text = "1step";
      d1->int_val = 0;
      d1->range.start = one_tok.loc;
    } else {
      lexer_.RestorePos(saved);
      d1 = ParsePrimaryExpr();
    }
  } else {
    d1 = ParsePrimaryExpr();
  }
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
    // Two-strength form: (strength0, strength1) or (strength1, strength0)
    // Single-strength form (pull gates): (strength0) or (strength1)
    if (IsStrength0Token(tk)) {
      str0 = ParseStrength0();
      if (Match(TokenKind::kComma)) str1 = ParseStrength1();
    } else {
      str1 = ParseStrength1();
      if (Match(TokenKind::kComma)) str0 = ParseStrength0();
    }
    Expect(TokenKind::kRParen);
  }

  Expr* delay = nullptr;
  Expr* delay_fall = nullptr;
  Expr* delay_decay = nullptr;
  ParseGateDelay(delay, delay_fall, delay_decay);

  // Parse comma-separated instances.
  auto* first = ParseOneGateInstance(gate_kind, loc);
  first->drive_strength0 = str0;
  first->drive_strength1 = str1;
  first->gate_delay = delay;
  first->gate_delay_fall = delay_fall;
  first->gate_delay_decay = delay_decay;
  items.push_back(first);

  while (Match(TokenKind::kComma)) {
    auto* next = ParseOneGateInstance(gate_kind, loc);
    next->drive_strength0 = str0;
    next->drive_strength1 = str1;
    next->gate_delay = delay;
    next->gate_delay_fall = delay_fall;
    next->gate_delay_decay = delay_decay;
    items.push_back(next);
  }
  Expect(TokenKind::kSemicolon);
}

// --- UDP instantiation (§A.5.4) ---

// Speculatively parse optional drive strength: (strength0, strength1) or
// (strength1, strength0).  Restores lexer position if '(' is not followed by
// a strength keyword.
bool Parser::TryParseStrengthSpec(uint8_t& str0, uint8_t& str1) {
  if (!Check(TokenKind::kLParen)) return false;
  auto saved = lexer_.SavePos();
  Consume();  // '('
  auto tk = CurrentToken().kind;
  if (!IsStrength0Token(tk) && !IsStrength1Token(tk)) {
    lexer_.RestorePos(saved);
    return false;
  }
  if (IsStrength0Token(tk)) {
    str0 = ParseStrength0();
    if (Match(TokenKind::kComma)) str1 = ParseStrength1();
  } else {
    str1 = ParseStrength1();
    if (Match(TokenKind::kComma)) str0 = ParseStrength0();
  }
  Expect(TokenKind::kRParen);
  return true;
}

// Parse a single UDP instance: optional name [ dimension ], then terminal list.
ModuleItem* Parser::ParseOneUdpInstance(const Token& udp_tok, SourceLoc loc) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kUdpInst;
  item->loc = loc;
  item->inst_module = udp_tok.text;

  // Optional name_of_instance: identifier [ unpacked_dimension ]
  if (CheckIdentifier() && !Check(TokenKind::kLParen)) {
    item->gate_inst_name = Consume().text;
    if (Check(TokenKind::kLBracket)) {
      Consume();
      item->inst_range_left = ParseExpr();
      if (Match(TokenKind::kColon)) {
        item->inst_range_right = ParseExpr();
      }
      Expect(TokenKind::kRBracket);
    }
  }

  // Terminal list: ( output_terminal , input_terminal { , input_terminal } )
  Expect(TokenKind::kLParen);
  item->gate_terminals.push_back(ParseExpr());
  while (Match(TokenKind::kComma)) {
    item->gate_terminals.push_back(ParseExpr());
  }
  Expect(TokenKind::kRParen);
  return item;
}

void Parser::ParseUdpInstList(const Token& udp_tok,
                              std::vector<ModuleItem*>& items) {
  auto loc = udp_tok.loc;

  // Optional drive_strength.
  uint8_t str0 = 0;
  uint8_t str1 = 0;
  TryParseStrengthSpec(str0, str1);

  // Optional delay2: #delay or #(rise, fall)
  Expr* delay = nullptr;
  Expr* delay_fall = nullptr;
  Expr* unused_decay = nullptr;
  ParseGateDelay(delay, delay_fall, unused_decay);

  // Parse comma-separated udp_instance entries.
  auto apply_common = [&](ModuleItem* item) {
    item->drive_strength0 = str0;
    item->drive_strength1 = str1;
    item->gate_delay = delay;
    item->gate_delay_fall = delay_fall;
  };

  auto* first = ParseOneUdpInstance(udp_tok, loc);
  apply_common(first);
  items.push_back(first);
  while (Match(TokenKind::kComma)) {
    auto* next = ParseOneUdpInstance(udp_tok, loc);
    apply_common(next);
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

char Parser::ParseUdpInitialValue(TokenKind stop1, TokenKind stop2) {
  char result = '0';
  while (!Check(stop1) && !Check(stop2) && !AtEnd()) {
    auto tok = Consume();
    if (!tok.text.empty()) {
      char last = tok.text.back();
      if (last == '0' || last == '1' || last == 'x' || last == 'X') {
        result = (last == 'X') ? 'x' : last;
      }
    }
  }
  return result;
}

void Parser::ParseUdpOutputDecl(UdpDecl* udp) {
  if (Match(TokenKind::kKwReg)) {
    udp->is_sequential = true;
  }
  udp->output_name = Expect(TokenKind::kIdentifier).text;
  if (Match(TokenKind::kEq)) {
    udp->has_initial = true;
    udp->initial_value =
        ParseUdpInitialValue(TokenKind::kSemicolon, TokenKind::kSemicolon);
  }
  Expect(TokenKind::kSemicolon);
}

void Parser::ParseUdpPortDecls(UdpDecl* udp) {
  while (!Check(TokenKind::kKwTable) && !Check(TokenKind::kKwInitial) &&
         !AtEnd()) {
    ParseAttributes();
    if (Match(TokenKind::kKwOutput)) {
      ParseUdpOutputDecl(udp);
    } else if (Match(TokenKind::kKwInput)) {
      udp->input_names.push_back(Expect(TokenKind::kIdentifier).text);
      while (Match(TokenKind::kComma)) {
        udp->input_names.push_back(Expect(TokenKind::kIdentifier).text);
      }
      Expect(TokenKind::kSemicolon);
    } else if (Match(TokenKind::kKwReg)) {
      udp->is_sequential = true;
      Expect(TokenKind::kIdentifier);
      Expect(TokenKind::kSemicolon);
    } else {
      break;
    }
  }
}

void Parser::ParseUdpTableRow(UdpDecl* udp) {
  UdpTableRow row;
  while (!Check(TokenKind::kColon) && !AtEnd()) {
    if (Check(TokenKind::kLParen)) {
      Consume();
      Token tok = Consume();
      char from = 0, to = 0;
      if (tok.text.size() >= 2) {
        from = tok.text[0];
        to = tok.text[1];
      } else {
        from = UdpCharFromToken(tok);
        to = UdpCharFromToken(Consume());
      }
      Expect(TokenKind::kRParen);
      while (row.paren_edges.size() < row.inputs.size()) {
        row.paren_edges.push_back({0, 0});
      }
      row.inputs.push_back('\x01');
      row.paren_edges.push_back({from, to});
    } else {
      row.inputs.push_back(UdpCharFromToken(Consume()));
    }
  }
  Expect(TokenKind::kColon);
  if (udp->is_sequential) {
    row.current_state = UdpCharFromToken(Consume());
    Expect(TokenKind::kColon);
  }
  row.output = UdpCharFromToken(Consume());
  Expect(TokenKind::kSemicolon);
  udp->table.push_back(row);
}

void Parser::ParseUdpTable(UdpDecl* udp) {
  Expect(TokenKind::kKwTable);
  while (!Check(TokenKind::kKwEndtable) && !AtEnd()) {
    ParseUdpTableRow(udp);
  }
  Expect(TokenKind::kKwEndtable);
}

UdpDecl* Parser::ParseUdpDecl() {
  auto* udp = arena_.Create<UdpDecl>();
  udp->range.start = CurrentLoc();
  Expect(TokenKind::kKwPrimitive);
  udp->name = Expect(TokenKind::kIdentifier).text;

  Expect(TokenKind::kLParen);
  if (Check(TokenKind::kDotStar)) {
    Consume();
    Expect(TokenKind::kRParen);
    Expect(TokenKind::kSemicolon);
    ParseUdpPortDecls(udp);
  } else if (Check(TokenKind::kKwOutput)) {
    Consume();
    if (Match(TokenKind::kKwReg)) {
      udp->is_sequential = true;
    }
    udp->output_name = Expect(TokenKind::kIdentifier).text;
    if (Match(TokenKind::kEq)) {
      udp->has_initial = true;
      udp->initial_value =
          ParseUdpInitialValue(TokenKind::kComma, TokenKind::kRParen);
    }
    while (Match(TokenKind::kComma)) {
      Match(TokenKind::kKwInput);
      udp->input_names.push_back(Expect(TokenKind::kIdentifier).text);
    }
    Expect(TokenKind::kRParen);
    Expect(TokenKind::kSemicolon);
  } else {
    Expect(TokenKind::kIdentifier);
    while (Match(TokenKind::kComma)) {
      Expect(TokenKind::kIdentifier);
    }
    Expect(TokenKind::kRParen);
    Expect(TokenKind::kSemicolon);
    ParseUdpPortDecls(udp);
  }

  if (Match(TokenKind::kKwInitial)) {
    udp->has_initial = true;
    Expect(TokenKind::kIdentifier);
    Expect(TokenKind::kEq);
    udp->initial_value =
        ParseUdpInitialValue(TokenKind::kSemicolon, TokenKind::kSemicolon);
    Expect(TokenKind::kSemicolon);
  }

  ParseUdpTable(udp);
  Expect(TokenKind::kKwEndprimitive);
  MatchEndLabel(udp->name);
  udp->range.end = CurrentLoc();
  return udp;
}

UdpDecl* Parser::ParseExternUdpDecl() {
  auto* udp = arena_.Create<UdpDecl>();
  udp->range.start = CurrentLoc();
  Expect(TokenKind::kKwPrimitive);
  udp->name = Expect(TokenKind::kIdentifier).text;

  // Port list (forward declaration only — no body/table).
  Expect(TokenKind::kLParen);
  if (Check(TokenKind::kKwOutput)) {
    // ANSI form: (output [reg] name, input in1, ...)
    Consume();
    if (Match(TokenKind::kKwReg)) {
      udp->is_sequential = true;
    }
    udp->output_name = Expect(TokenKind::kIdentifier).text;
    while (Match(TokenKind::kComma)) {
      Match(TokenKind::kKwInput);
      udp->input_names.push_back(Expect(TokenKind::kIdentifier).text);
    }
  } else {
    // Non-ANSI form: plain identifiers
    udp->output_name = Expect(TokenKind::kIdentifier).text;
    while (Match(TokenKind::kComma)) {
      udp->input_names.push_back(Expect(TokenKind::kIdentifier).text);
    }
  }
  Expect(TokenKind::kRParen);
  Expect(TokenKind::kSemicolon);
  udp->range.end = CurrentLoc();
  return udp;
}

}  // namespace delta
