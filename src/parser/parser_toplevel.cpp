#include "parser/parser.h"
#include "parser/parser_instance_internal.h"

namespace delta {

void ParseGateInstanceTail(Parser& p, ModuleItem* item, bool has_name) {
  if (has_name) {
    item->gate_inst_name = p.Consume().text;
    if (p.Check(TokenKind::kLBracket)) {
      p.Consume();
      item->inst_range_left = p.ParseExpr();
      if (p.Match(TokenKind::kColon)) {
        item->inst_range_right = p.ParseExpr();
      }
      p.Expect(TokenKind::kRBracket);
    }
  }

  p.Expect(TokenKind::kLParen);
  item->gate_terminals.push_back(p.ParseExpr());
  while (p.Match(TokenKind::kComma)) {
    item->gate_terminals.push_back(p.ParseExpr());
  }
  p.Expect(TokenKind::kRParen);
}

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

static void ValidateInoutNetLvalues(const std::vector<Expr*>& terms,
                                    DiagEngine& diag, SourceLoc loc) {
  for (size_t i = 0; i < terms.size() && i < 2; ++i)
    if (!IsNetLvalue(terms[i]))
      diag.Error(loc, "inout terminal must be a net lvalue");
}

static void ValidateOutputNetLvalues(const std::vector<Expr*>& terms,
                                     DiagEngine& diag, SourceLoc loc) {
  for (size_t i = 0; i + 1 < terms.size(); ++i)
    if (!IsNetLvalue(terms[i]))
      diag.Error(loc, "output terminal must be a net lvalue");
}

static void ValidateGateTerminalLvalues(GateKind kind,
                                        const std::vector<Expr*>& terms,
                                        DiagEngine& diag, SourceLoc loc) {
  if (terms.empty()) return;
  switch (kind) {
    case GateKind::kTran:
    case GateKind::kRtran:

      ValidateInoutNetLvalues(terms, diag, loc);
      break;
    case GateKind::kTranif0:
    case GateKind::kTranif1:
    case GateKind::kRtranif0:
    case GateKind::kRtranif1:

      ValidateInoutNetLvalues(terms, diag, loc);
      break;
    case GateKind::kBuf:
    case GateKind::kNot:

      ValidateOutputNetLvalues(terms, diag, loc);
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

      if (!IsNetLvalue(terms[0]))
        diag.Error(loc, "output terminal must be a net lvalue");
      break;
  }
}

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

static void CheckGateArrayNameUnique(ModuleItem* mi,
                                     std::vector<std::string_view>& array_names,
                                     DiagEngine& diag) {
  if (mi->gate_inst_name.empty() || mi->inst_range_left == nullptr) return;
  for (const auto& n : array_names) {
    if (n == mi->gate_inst_name) {
      diag.Error(mi->loc,
                 "instance identifier reused for another array of "
                 "instances in the same declaration");
      return;
    }
  }
  array_names.push_back(mi->gate_inst_name);
}

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

  std::vector<std::string_view> array_names;
  while (Match(TokenKind::kComma)) {
    auto* next = ParseOneGateInstance(kind, loc);
    CheckGateArrayNameUnique(next, array_names, diag_);
    items.push_back(next);
  }
  Expect(TokenKind::kSemicolon);
}

ModuleItem* Parser::ParseOneGateInstance(GateKind kind, SourceLoc loc) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kGateInst;
  item->loc = loc;
  item->gate_kind = kind;

  ParseGateInstanceTail(*this, item, Check(TokenKind::kIdentifier));
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

static void ValidateGateStrength(GateKind gate_kind, SourceLoc loc,
                                 uint8_t str0, uint8_t str1, DiagEngine& diag) {
  if (!GateAllowsStrength(gate_kind))
    diag.Error(loc, "drive strength not allowed on this gate type");

  if (gate_kind == GateKind::kPulldown && str0 == 0 && str1 != 0)
    diag.Error(loc, "pulldown single-strength must be a strength0 keyword");
  if (gate_kind == GateKind::kPullup && str1 == 0 && str0 != 0)
    diag.Error(loc, "pullup single-strength must be a strength1 keyword");

  if (GateAllowsStrength(gate_kind) && gate_kind != GateKind::kPullup &&
      gate_kind != GateKind::kPulldown && (str0 == 0 || str1 == 0))
    diag.Error(loc,
               "drive strength on this gate type requires both a "
               "strength0 and a strength1 keyword");
}

void Parser::ParseGateInst(std::vector<ModuleItem*>& items) {
  auto loc = CurrentLoc();
  auto gate_kind = TokenToGateKind(CurrentToken().kind);
  Consume();

  uint8_t str0 = 0;
  uint8_t str1 = 0;
  bool has_strength = false;
  if (Check(TokenKind::kLParen)) {
    Consume();
    auto tk = CurrentToken().kind;
    has_strength = IsStrength0Token(tk) || IsStrength1Token(tk);
    if (!has_strength) {
      ParseInlineGateTerminals(gate_kind, loc, items);
      return;
    }

    if (IsStrength0Token(tk)) {
      str0 = ParseStrength0();
      if (Match(TokenKind::kComma)) str1 = ParseStrength1();
    } else {
      str1 = ParseStrength1();
      if (Match(TokenKind::kComma)) str0 = ParseStrength0();
    }
    Expect(TokenKind::kRParen);
    ValidateGateStrength(gate_kind, loc, str0, str1, diag_);
  }

  Expr* delay = nullptr;
  Expr* delay_fall = nullptr;
  Expr* delay_decay = nullptr;
  ParseGateDelay(delay, delay_fall, delay_decay);
  if (delay && !GateAllowsDelay(gate_kind))
    diag_.Error(loc, "delay not allowed on this gate type");
  if (delay_decay && !GateUsesDelay3(gate_kind))
    diag_.Error(loc, "this gate type allows at most 2 delay values");

  std::vector<std::string_view> array_names;
  auto parse_instance = [&]() -> ModuleItem* {
    auto* mi = ParseOneGateInstance(gate_kind, loc);
    mi->drive_strength0 = str0;
    mi->drive_strength1 = str1;
    mi->gate_delay = delay;
    mi->gate_delay_fall = delay_fall;
    mi->gate_delay_decay = delay_decay;
    CheckGateArrayNameUnique(mi, array_names, diag_);
    return mi;
  };

  items.push_back(parse_instance());
  while (Match(TokenKind::kComma)) {
    items.push_back(parse_instance());
  }
  Expect(TokenKind::kSemicolon);
}

bool Parser::TryParseStrengthSpec(uint8_t& str0, uint8_t& str1) {
  if (!Check(TokenKind::kLParen)) return false;
  auto saved = lexer_.SavePos();
  Consume();
  auto tk = CurrentToken().kind;
  if (!IsStrength0Token(tk) && !IsStrength1Token(tk)) {
    lexer_.RestorePos(saved);
    return false;
  }
  auto loc = CurrentLoc();
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

  if (str0 == 0 || str1 == 0) {
    diag_.Error(loc,
                "drive_strength requires one strength0 keyword and "
                "one strength1 keyword");
  }
  return true;
}

}  // namespace delta
