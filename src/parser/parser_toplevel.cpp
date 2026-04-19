#include "parser/parser.h"

namespace delta {

// --- Gate primitive parsing ---

// §A.3.1: Which gate categories allow drive_strength.
static bool GateAllowsStrength(GateKind kind) {
  switch (kind) {
    case GateKind::kAnd:
    case GateKind::kNand:
    case GateKind::kOr:
    case GateKind::kNor:
    case GateKind::kXor:
    case GateKind::kXnor:
    case GateKind::kBuf:
    case GateKind::kNot:
    case GateKind::kBufif0:
    case GateKind::kBufif1:
    case GateKind::kNotif0:
    case GateKind::kNotif1:
    case GateKind::kPullup:
    case GateKind::kPulldown:
      return true;
    default:
      return false;
  }
}

// §A.3.1: Which gate categories allow delay.
static bool GateAllowsDelay(GateKind kind) {
  switch (kind) {
    case GateKind::kTran:
    case GateKind::kRtran:
    case GateKind::kPullup:
    case GateKind::kPulldown:
      return false;
    default:
      return true;
  }
}

// §A.3.1: Whether the gate uses delay3 (true) or delay2 (false).
static bool GateUsesDelay3(GateKind kind) {
  switch (kind) {
    case GateKind::kCmos:
    case GateKind::kRcmos:
    case GateKind::kNmos:
    case GateKind::kPmos:
    case GateKind::kRnmos:
    case GateKind::kRpmos:
    case GateKind::kBufif0:
    case GateKind::kBufif1:
    case GateKind::kNotif0:
    case GateKind::kNotif1:
      return true;
    default:
      return false;
  }
}

// §A.8.5: Check whether an expression is a valid net_lvalue.
static bool IsNetLvalue(const Expr* e) {
  switch (e->kind) {
    case ExprKind::kIdentifier:
    case ExprKind::kSelect:
    case ExprKind::kMemberAccess:
      return true;
    case ExprKind::kConcatenation:
      for (auto* child : e->elements)
        if (!IsNetLvalue(child)) return false;
      return true;
    case ExprKind::kAssignmentPattern:
      for (auto* child : e->elements)
        if (!IsNetLvalue(child)) return false;
      return true;
    case ExprKind::kCast:
      return e->lhs && e->lhs->kind == ExprKind::kAssignmentPattern &&
             IsNetLvalue(e->lhs);
    default:
      return false;
  }
}

// §A.3.3: Validate that output_terminal and inout_terminal positions contain
// net_lvalue expressions.
static void ValidateGateTerminalLvalues(GateKind kind,
                                        const std::vector<Expr*>& terms,
                                        DiagEngine& diag, SourceLoc loc) {
  if (terms.empty()) return;
  switch (kind) {
    case GateKind::kTran:
    case GateKind::kRtran:
      // ( inout_terminal , inout_terminal )
      for (size_t i = 0; i < terms.size() && i < 2; ++i)
        if (!IsNetLvalue(terms[i]))
          diag.Error(loc, "inout terminal must be a net lvalue");
      break;
    case GateKind::kTranif0:
    case GateKind::kTranif1:
    case GateKind::kRtranif0:
    case GateKind::kRtranif1:
      // ( inout_terminal , inout_terminal , enable_terminal )
      for (size_t i = 0; i < terms.size() && i < 2; ++i)
        if (!IsNetLvalue(terms[i]))
          diag.Error(loc, "inout terminal must be a net lvalue");
      break;
    case GateKind::kBuf:
    case GateKind::kNot:
      // ( output_terminal { , output_terminal } , input_terminal )
      for (size_t i = 0; i + 1 < terms.size(); ++i)
        if (!IsNetLvalue(terms[i]))
          diag.Error(loc, "output terminal must be a net lvalue");
      break;
    case GateKind::kPullup:
    case GateKind::kPulldown:
    case GateKind::kAnd:
    case GateKind::kNand:
    case GateKind::kOr:
    case GateKind::kNor:
    case GateKind::kXor:
    case GateKind::kXnor:
    case GateKind::kBufif0:
    case GateKind::kBufif1:
    case GateKind::kNotif0:
    case GateKind::kNotif1:
    case GateKind::kNmos:
    case GateKind::kPmos:
    case GateKind::kRnmos:
    case GateKind::kRpmos:
    case GateKind::kCmos:
    case GateKind::kRcmos:
      // First terminal is output_terminal.
      if (!IsNetLvalue(terms[0]))
        diag.Error(loc, "output terminal must be a net lvalue");
      break;
  }
}

// §A.3.1: Validate terminal count for a gate instance.
static bool ValidGateTerminalCount(GateKind kind, size_t count) {
  switch (kind) {
    case GateKind::kCmos:
    case GateKind::kRcmos:
      return count == 4;
    case GateKind::kNmos:
    case GateKind::kPmos:
    case GateKind::kRnmos:
    case GateKind::kRpmos:
    case GateKind::kBufif0:
    case GateKind::kBufif1:
    case GateKind::kNotif0:
    case GateKind::kNotif1:
    case GateKind::kTranif0:
    case GateKind::kTranif1:
    case GateKind::kRtranif0:
    case GateKind::kRtranif1:
      return count == 3;
    case GateKind::kTran:
    case GateKind::kRtran:
      return count == 2;
    case GateKind::kPullup:
    case GateKind::kPulldown:
      return count == 1;
    case GateKind::kAnd:
    case GateKind::kNand:
    case GateKind::kOr:
    case GateKind::kNor:
    case GateKind::kXor:
    case GateKind::kXnor:
      return count >= 2;
    case GateKind::kBuf:
    case GateKind::kNot:
      return count >= 2;
  }
  return true;
}

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
  if (!ValidGateTerminalCount(kind, item->gate_terminals.size()))
    diag_.Error(loc, "incorrect number of terminals for gate instance");
  ValidateGateTerminalLvalues(kind, item->gate_terminals, diag_, loc);
  items.push_back(item);
  // First instance here is unnamed (anonymous); follow-ups may be arrays and
  // must obey the one-identifier-per-range rule.
  std::vector<std::string_view> array_names;
  while (Match(TokenKind::kComma)) {
    auto* next = ParseOneGateInstance(kind, loc);
    if (!next->gate_inst_name.empty() && next->inst_range_left != nullptr) {
      bool dup = false;
      for (auto n : array_names) {
        if (n == next->gate_inst_name) {
          dup = true;
          break;
        }
      }
      if (dup) {
        diag_.Error(next->loc,
                    "instance identifier reused for another array of "
                    "instances in the same declaration");
      } else {
        array_names.push_back(next->gate_inst_name);
      }
    }
    items.push_back(next);
  }
  Expect(TokenKind::kSemicolon);
}

ModuleItem* Parser::ParseOneGateInstance(GateKind kind, SourceLoc loc) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kGateInst;
  item->loc = loc;
  item->gate_kind = kind;

  // Optional name_of_instance: instance_identifier [ unpacked_dimension ].
  if (Check(TokenKind::kIdentifier)) {
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

  // Terminal list.
  Expect(TokenKind::kLParen);
  item->gate_terminals.push_back(ParseExpr());
  while (Match(TokenKind::kComma)) {
    item->gate_terminals.push_back(ParseExpr());
  }
  Expect(TokenKind::kRParen);
  if (!ValidGateTerminalCount(kind, item->gate_terminals.size()))
    diag_.Error(loc, "incorrect number of terminals for gate instance");
  ValidateGateTerminalLvalues(kind, item->gate_terminals, diag_, loc);
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
    if (!GateAllowsStrength(gate_kind))
      diag_.Error(loc, "drive strength not allowed on this gate type");
    // §A.3.2: single-strength pulldown must use strength0, pullup must use
    // strength1.
    if (gate_kind == GateKind::kPulldown && str0 == 0 && str1 != 0)
      diag_.Error(loc,
                  "pulldown single-strength must be a strength0 keyword");
    if (gate_kind == GateKind::kPullup && str1 == 0 && str0 != 0)
      diag_.Error(loc,
                  "pullup single-strength must be a strength1 keyword");
    // Every gate except pullup/pulldown requires both a strength0 and a
    // strength1 keyword; a single-strength form is not allowed for them.
    if (GateAllowsStrength(gate_kind) && gate_kind != GateKind::kPullup &&
        gate_kind != GateKind::kPulldown && (str0 == 0 || str1 == 0))
      diag_.Error(loc,
                  "drive strength on this gate type requires both a "
                  "strength0 and a strength1 keyword");
  }

  Expr* delay = nullptr;
  Expr* delay_fall = nullptr;
  Expr* delay_decay = nullptr;
  ParseGateDelay(delay, delay_fall, delay_decay);
  if (delay && !GateAllowsDelay(gate_kind))
    diag_.Error(loc, "delay not allowed on this gate type");
  if (delay_decay && !GateUsesDelay3(gate_kind))
    diag_.Error(loc, "this gate type allows at most 2 delay values");

  // Track array instance identifiers declared in this statement; an identifier
  // may associate with only one range specification.
  std::vector<std::string_view> array_names;
  auto check_continuous_range = [&](ModuleItem* mi) {
    if (mi->gate_inst_name.empty() || mi->inst_range_left == nullptr) return;
    for (const auto& n : array_names) {
      if (n == mi->gate_inst_name) {
        diag_.Error(mi->loc,
                    "instance identifier reused for another array of "
                    "instances in the same declaration");
        return;
      }
    }
    array_names.push_back(mi->gate_inst_name);
  };

  // Parse comma-separated instances.
  auto* first = ParseOneGateInstance(gate_kind, loc);
  first->drive_strength0 = str0;
  first->drive_strength1 = str1;
  first->gate_delay = delay;
  first->gate_delay_fall = delay_fall;
  first->gate_delay_decay = delay_decay;
  check_continuous_range(first);
  items.push_back(first);

  while (Match(TokenKind::kComma)) {
    auto* next = ParseOneGateInstance(gate_kind, loc);
    next->drive_strength0 = str0;
    next->drive_strength1 = str1;
    next->gate_delay = delay;
    next->gate_delay_fall = delay_fall;
    next->gate_delay_decay = delay_decay;
    check_continuous_range(next);
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

void Parser::RejectUdpPortDimension() {
  // §29.3.1: a UDP port shall be scalar; skip any range so the rest of the
  // port declaration can still parse.
  if (!Check(TokenKind::kLBracket)) return;
  diag_.Error(CurrentLoc(),
              "UDP port shall be scalar; vector range not permitted");
  int depth = 0;
  do {
    if (Check(TokenKind::kLBracket))
      ++depth;
    else if (Check(TokenKind::kRBracket))
      --depth;
    Consume();
  } while (depth > 0 && !AtEnd());
}

void Parser::RejectUdpInoutPort() {
  // §29.3.1: bidirectional ports are not legal on a UDP.
  diag_.Error(CurrentLoc(),
              "UDP ports shall be input or output; inout not permitted");
  Consume();
}

void Parser::ValidateUdpHeader(UdpDecl* udp) {
  // §29.3.1: every UDP has exactly one output and one or more inputs.
  if (udp->output_name.empty()) {
    diag_.Error(udp->range.start, "UDP shall have exactly one output port");
  }
  if (udp->input_names.empty()) {
    diag_.Error(udp->range.start, "UDP shall have at least one input port");
  }
}

void Parser::ValidateUdpTable(UdpDecl* udp) {
  // §29.3.4: the same combination of inputs (and current state, when
  // sequential) shall not specify different outputs on two different rows.
  for (size_t i = 0; i < udp->table.size(); ++i) {
    for (size_t j = i + 1; j < udp->table.size(); ++j) {
      const auto& a = udp->table[i];
      const auto& b = udp->table[j];
      if (a.inputs == b.inputs && a.paren_edges == b.paren_edges &&
          a.current_state == b.current_state && a.output != b.output) {
        diag_.Error(udp->range.start,
                    "UDP table rows with identical inputs shall not specify "
                    "different outputs");
        return;
      }
    }
  }
}

static char UdpCharFromToken(const Token& tok) {
  if (tok.kind == TokenKind::kStar) return '*';
  if (tok.kind == TokenKind::kMinus) return '-';
  if (tok.kind == TokenKind::kQuestion) return '?';
  if (!tok.text.empty()) return tok.text[0];
  return '?';
}

static bool UdpInputIsEdge(char c) {
  // Single-char edge symbols plus the \x01 placeholder for parenthesized
  // edge indicators.
  if (c == 'r' || c == 'R' || c == 'f' || c == 'F') return true;
  if (c == 'p' || c == 'P' || c == 'n' || c == 'N') return true;
  if (c == '*' || c == '\x01') return true;
  return false;
}

static bool UdpSymbolIsZ(char c) { return c == 'z' || c == 'Z'; }

static bool UdpIsLevelSymbol(char c) {
  return c == '0' || c == '1' || c == 'x' || c == 'X' ||
         c == '?' || c == 'b' || c == 'B';
}

static bool IsValidUdpInitialLiteral(std::string_view text) {
  if (text == "0" || text == "1") return true;
  if (text.size() == 4 && text[0] == '1' && text[1] == '\'' &&
      (text[2] == 'b' || text[2] == 'B')) {
    char d = text[3];
    return d == '0' || d == '1' || d == 'x' || d == 'X';
  }
  return false;
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
  RejectUdpPortDimension();
  auto id_tok = Expect(TokenKind::kIdentifier);
  // §29.3.1: a UDP has exactly one output port.
  if (!udp->output_name.empty()) {
    diag_.Error(id_tok.loc, "UDP shall have exactly one output port");
  }
  udp->output_name = id_tok.text;
  if (Match(TokenKind::kEq)) {
    udp->has_initial = true;
    udp->initial_value =
        ParseUdpInitialValue(TokenKind::kSemicolon, TokenKind::kSemicolon);
  }
  Expect(TokenKind::kSemicolon);
}

void Parser::ParseUdpPortDecls(UdpDecl* udp) {
  // Record each reg declaration's identifier so the reg-names-the-output
  // check can run after the output port declaration has been seen, since
  // the reg and output declarations may appear in either order.
  struct PendingReg {
    std::string_view name;
    SourceLoc loc;
  };
  std::vector<PendingReg> reg_decls;
  while (!Check(TokenKind::kKwTable) && !Check(TokenKind::kKwInitial) &&
         !AtEnd()) {
    ParseAttributes();
    if (Match(TokenKind::kKwOutput)) {
      ParseUdpOutputDecl(udp);
    } else if (Match(TokenKind::kKwInput)) {
      RejectUdpPortDimension();
      udp->input_names.push_back(Expect(TokenKind::kIdentifier).text);
      while (Match(TokenKind::kComma)) {
        RejectUdpPortDimension();
        udp->input_names.push_back(Expect(TokenKind::kIdentifier).text);
      }
      Expect(TokenKind::kSemicolon);
    } else if (Match(TokenKind::kKwReg)) {
      udp->is_sequential = true;
      auto id_tok = Expect(TokenKind::kIdentifier);
      reg_decls.push_back({id_tok.text, id_tok.loc});
      Expect(TokenKind::kSemicolon);
    } else if (Check(TokenKind::kKwInout)) {
      RejectUdpInoutPort();
      // Recover by skipping to the terminating semicolon.
      while (!Check(TokenKind::kSemicolon) && !AtEnd()) Consume();
      Match(TokenKind::kSemicolon);
    } else {
      break;
    }
  }
  // §29.3.2: a reg declaration in a UDP body must name the output port.
  for (const auto& reg : reg_decls) {
    if (!udp->output_name.empty() && reg.name != udp->output_name) {
      diag_.Error(reg.loc,
                  "UDP reg declaration shall name the output port");
    }
  }
}

void Parser::ParseUdpTableRow(UdpDecl* udp) {
  UdpTableRow row;
  SourceLoc row_loc = CurrentLoc();
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

  // §29.3.4: the z state is excluded from UDP tables.
  bool saw_z = false;
  for (char c : row.inputs) {
    if (UdpSymbolIsZ(c)) saw_z = true;
  }
  for (const auto& pe : row.paren_edges) {
    if (UdpSymbolIsZ(pe.first) || UdpSymbolIsZ(pe.second)) saw_z = true;
  }
  if (UdpSymbolIsZ(row.current_state) || UdpSymbolIsZ(row.output)) {
    saw_z = true;
  }
  if (saw_z) {
    diag_.Error(row_loc, "UDP table row shall not contain z");
  }

  // §29.3.4: at most one input transition per row.
  int edge_count = 0;
  for (char c : row.inputs) {
    if (UdpInputIsEdge(c)) ++edge_count;
  }
  if (edge_count > 1) {
    diag_.Error(row_loc,
                "UDP table row shall contain at most one input transition");
  }

  // §29.3.4: all-x input row shall specify x as the output.
  if (!row.inputs.empty()) {
    bool all_x = true;
    for (char c : row.inputs) {
      if (c != 'x' && c != 'X') {
        all_x = false;
        break;
      }
    }
    if (all_x && row.output != 'x' && row.output != 'X') {
      diag_.Error(row_loc,
                  "UDP table row with all-x inputs shall specify x output");
    }
  }

  // §29.3.6: - is confined to the output field of a sequential row.
  for (char c : row.inputs) {
    if (c == '-') {
      diag_.Error(row_loc, "- shall not appear in a UDP input field");
      break;
    }
  }
  if (udp->is_sequential) {
    char cs = row.current_state;
    if (cs == '-') {
      diag_.Error(row_loc, "- shall not appear in the current-state field");
    } else if (UdpInputIsEdge(cs)) {
      diag_.Error(row_loc,
                  "edge symbols shall not appear in the current-state field");
    }
  }

  // §29.3.6: output field is 0/1/x; sequential UDPs additionally accept -.
  {
    char out = row.output;
    bool ok = (out == '0' || out == '1' || out == 'x' || out == 'X');
    if (udp->is_sequential && out == '-') ok = true;
    if (!ok) {
      diag_.Error(row_loc,
                  "UDP output field shall be 0, 1, or x (- is sequential only)");
    }
  }

  // §29.3.6: (vw) edge endpoints must be level symbols.
  for (const auto& pe : row.paren_edges) {
    if (pe.first == 0 && pe.second == 0) continue;
    if (!UdpIsLevelSymbol(pe.first) || !UdpIsLevelSymbol(pe.second)) {
      diag_.Error(row_loc,
                  "parenthesized edge endpoints shall be level symbols");
      break;
    }
  }

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
  } else {
    ParseAttributes();
    if (Check(TokenKind::kKwInout)) {
      // §29.3.1: output must be the first port, and inout is never legal.
      RejectUdpInoutPort();
    }
    if (Check(TokenKind::kKwOutput)) {
      Consume();
      if (Match(TokenKind::kKwReg)) {
        udp->is_sequential = true;
      }
      RejectUdpPortDimension();
      udp->output_name = Expect(TokenKind::kIdentifier).text;
      if (Match(TokenKind::kEq)) {
        udp->has_initial = true;
        udp->initial_value =
            ParseUdpInitialValue(TokenKind::kComma, TokenKind::kRParen);
      }
      while (Match(TokenKind::kComma)) {
        ParseAttributes();
        if (Check(TokenKind::kKwInout)) {
          RejectUdpInoutPort();
        } else {
          Match(TokenKind::kKwInput);
        }
        RejectUdpPortDimension();
        udp->input_names.push_back(Expect(TokenKind::kIdentifier).text);
      }
      Expect(TokenKind::kRParen);
      Expect(TokenKind::kSemicolon);
    } else {
      // Non-ANSI port list: plain identifiers. §29.3.1 requires that the
      // first of these identifies the output port; remember it so the
      // subsequent declarations can be checked.
      auto first_tok = Expect(TokenKind::kIdentifier);
      std::string_view first_name = first_tok.text;
      SourceLoc first_loc = first_tok.loc;
      std::vector<std::string_view> port_list_inputs;
      while (Match(TokenKind::kComma)) {
        port_list_inputs.push_back(Expect(TokenKind::kIdentifier).text);
      }
      Expect(TokenKind::kRParen);
      Expect(TokenKind::kSemicolon);
      ParseUdpPortDecls(udp);
      if (!udp->output_name.empty() && !first_name.empty() &&
          first_name != udp->output_name) {
        diag_.Error(first_loc,
                    "UDP output port shall be the first port in the port list");
      }
      // §29.3.4: input field positions in the state table follow the port
      // list in the header, not the order of the input port declarations.
      std::vector<std::string_view> reordered;
      reordered.reserve(port_list_inputs.size());
      for (auto name : port_list_inputs) {
        for (auto decl_name : udp->input_names) {
          if (decl_name == name) {
            reordered.push_back(decl_name);
            break;
          }
        }
      }
      if (reordered.size() == udp->input_names.size()) {
        udp->input_names = std::move(reordered);
      }
    }
  }

  if (Match(TokenKind::kKwInitial)) {
    udp->has_initial = true;
    // §29.7: the body is a single procedural assignment; a sequential
    // block introduces multiple statements and is not permitted.
    if (Check(TokenKind::kKwBegin)) {
      diag_.Error(
          CurrentLoc(),
          "UDP initial statement shall be a single procedural assignment");
    }
    // §29.7: no delay control may precede the assignment.
    if (Check(TokenKind::kHash)) {
      diag_.Error(CurrentLoc(),
                  "UDP initial statement shall not contain delay control");
    }
    auto id_tok = Expect(TokenKind::kIdentifier);
    // §29.3.3: the initial statement assigns to the output port.
    if (!udp->output_name.empty() && id_tok.text != udp->output_name) {
      diag_.Error(id_tok.loc,
                  "UDP initial statement shall target the output port");
    }
    Expect(TokenKind::kEq);
    // §29.7: the RHS is restricted to 0, 1, or the single-bit sized
    // forms 1'b0, 1'b1, 1'bx, 1'bX (and capitalized base specifier).
    auto rhs_tok = CurrentToken();
    udp->initial_value = ParseUdpInitialValue(TokenKind::kSemicolon,
                                              TokenKind::kSemicolon);
    if (!IsValidUdpInitialLiteral(rhs_tok.text)) {
      diag_.Error(rhs_tok.loc,
                  "UDP initial statement RHS shall be 0, 1, or a single-bit "
                  "literal");
    }
    Expect(TokenKind::kSemicolon);
  }

  ParseUdpTable(udp);
  Expect(TokenKind::kKwEndprimitive);
  MatchEndLabel(udp->name);
  udp->range.end = CurrentLoc();
  ValidateUdpHeader(udp);
  ValidateUdpTable(udp);
  return udp;
}

UdpDecl* Parser::ParseExternUdpDecl() {
  auto* udp = arena_.Create<UdpDecl>();
  udp->range.start = CurrentLoc();
  Expect(TokenKind::kKwPrimitive);
  udp->name = Expect(TokenKind::kIdentifier).text;

  // Port list (forward declaration only — no body/table).
  Expect(TokenKind::kLParen);
  ParseAttributes();
  if (Check(TokenKind::kKwInout)) {
    RejectUdpInoutPort();
  }
  if (Check(TokenKind::kKwOutput)) {
    // ANSI form: (output [reg] name, input in1, ...)
    Consume();
    if (Match(TokenKind::kKwReg)) {
      udp->is_sequential = true;
    }
    RejectUdpPortDimension();
    udp->output_name = Expect(TokenKind::kIdentifier).text;
    while (Match(TokenKind::kComma)) {
      ParseAttributes();
      if (Check(TokenKind::kKwInout)) {
        RejectUdpInoutPort();
      } else {
        Match(TokenKind::kKwInput);
      }
      RejectUdpPortDimension();
      udp->input_names.push_back(Expect(TokenKind::kIdentifier).text);
    }
  } else {
    // Non-ANSI form: plain identifiers. The first identifier names the
    // output port per §29.3.1.
    udp->output_name = Expect(TokenKind::kIdentifier).text;
    while (Match(TokenKind::kComma)) {
      udp->input_names.push_back(Expect(TokenKind::kIdentifier).text);
    }
  }
  Expect(TokenKind::kRParen);
  Expect(TokenKind::kSemicolon);
  udp->range.end = CurrentLoc();
  ValidateUdpHeader(udp);
  return udp;
}

}  // namespace delta
