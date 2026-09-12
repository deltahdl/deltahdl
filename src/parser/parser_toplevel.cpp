#include "parser/parser.h"
#include "parser/parser_instance_internal.h"

namespace delta {

// The `[ ... ]` after an instance name. A.4.1.1's name_of_instance is
// `instance_identifier { unpacked_dimension }`, and §28.3.5 gives the one
// unpacked_dimension an array of instances takes: "the range shall be
// specified by two constant expressions, left-hand index (lhi) and right-hand
// index (rhi), separated by a colon and enclosed within a pair of square
// brackets", and "one instance identifier shall be associated with only one
// range". The first range is recorded; a size alone, A.2.5's `[
// constant_expression ]`, is reported where its colon was due and the
// instance is one, as it was; and every range after the first is reported
// and read past.
void Parser::ParseInstanceRange(ModuleItem* item, bool first) {
  Expect(TokenKind::kLBracket, Subclause("28.3.5"));
  Expr* left = ParseExpr();
  Expr* right = nullptr;
  if (Match(TokenKind::kColon)) {
    right = ParseExpr();
  } else {
    diag_.Error(CurrentLoc(),
                "an array of instances is declared by a range of two "
                "constant expressions, [lhi:rhi]; a size alone is no range",
                Subclause("28.3.5"));
  }
  Expect(TokenKind::kRBracket, Subclause("28.3.5"));
  if (!first) return;
  item->inst_range_left = left;
  item->inst_range_right = right;
}

void ParseGateInstanceTail(Parser& p, ModuleItem* item, bool has_name) {
  if (has_name) {
    item->gate_inst_name = p.Consume().text;
    if (p.Check(TokenKind::kLBracket)) p.ParseInstanceRange(item, true);
    while (p.Check(TokenKind::kLBracket)) {
      p.diag_.Error(p.CurrentLoc(),
                    "one instance identifier shall be associated with only "
                    "one range to declare an array of instances",
                    Subclause("28.3.5"));
      p.ParseInstanceRange(item, false);
    }
  }

  p.Expect(TokenKind::kLParen, Subclause("28.3.6"));
  item->gate_terminals.push_back(p.ParseExpr());
  while (p.Match(TokenKind::kComma)) {
    item->gate_terminals.push_back(p.ParseExpr());
  }
  p.Expect(TokenKind::kRParen, Subclause("28.3.6"));
}

// What A.3.1 lets an instance of each A.3.4 type carry. n_input_gate_instance
// and n_output_gate_instance are written `[ drive_strength ] [ delay2 ]`,
// enable_gate_instance `[ drive_strength ] [ delay3 ]`, mos_switch_instance
// and cmos_switch_instance `[ delay3 ]`, pass_en_switch_instance `[ delay2 ]`,
// pass_switch_instance nothing, and the pull gates `[ pullup_strength ]` and
// `[ pulldown_strength ]` alone.
static bool GateAllowsStrength(GateKind kind) {
  switch (GateTypeOf(kind)) {
    case GateType::kNInputGate:
    case GateType::kNOutputGate:
    case GateType::kEnableGate:
    case GateType::kPullGate:
      return true;
    default:
      return false;
  }
}

static bool GateAllowsDelay(GateKind kind) {
  GateType type = GateTypeOf(kind);
  return type != GateType::kPassSwitch && type != GateType::kPullGate;
}

static bool GateUsesDelay3(GateKind kind) {
  switch (GateTypeOf(kind)) {
    case GateType::kCmosSwitch:
    case GateType::kMosSwitch:
    case GateType::kEnableGate:
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
      diag.Error(loc, "inout terminal must be a net lvalue", Subclause("28.3"));
}

static void ValidateOutputNetLvalues(const std::vector<Expr*>& terms,
                                     DiagEngine& diag, SourceLoc loc) {
  for (size_t i = 0; i + 1 < terms.size(); ++i)
    if (!IsNetLvalue(terms[i]))
      diag.Error(loc, "output terminal must be a net lvalue",
                 Subclause("28.3"));
}

// The terminals A.3.3 makes a net_lvalue, by the instance form A.3.1 gives
// each A.3.4 type: the two inout_terminals a pass_switch_instance or
// pass_en_switch_instance opens with, every output_terminal of an
// n_output_gate_instance, which is each terminal but the last, and the one
// output_terminal every other instance opens with. The enable_terminal,
// input_terminal, ncontrol_terminal and pcontrol_terminal after them are
// expressions, and are left as read.
static void ValidateGateTerminalLvalues(GateKind kind,
                                        const std::vector<Expr*>& terms,
                                        DiagEngine& diag, SourceLoc loc) {
  if (terms.empty()) return;
  switch (GateTypeOf(kind)) {
    case GateType::kPassSwitch:
    case GateType::kPassEnSwitch:
      ValidateInoutNetLvalues(terms, diag, loc);
      break;
    case GateType::kNOutputGate:
      ValidateOutputNetLvalues(terms, diag, loc);
      break;
    default:
      if (!IsNetLvalue(terms[0]))
        diag.Error(loc, "output terminal must be a net lvalue",
                   Subclause("28.3"));
      break;
  }
}

// The terminals A.3.1 gives an instance of each A.3.4 type:
// cmos_switch_instance four, mos_switch_instance, enable_gate_instance and
// pass_en_switch_instance three, pass_switch_instance two, pull_gate_instance
// one, and n_input_gate_instance `output_terminal , input_terminal { ,
// input_terminal
// }` and n_output_gate_instance `output_terminal { , output_terminal } ,
// input_terminal`, two at least.
static bool ValidGateTerminalCount(GateKind kind, size_t count) {
  switch (GateTypeOf(kind)) {
    case GateType::kCmosSwitch:
      return count == 4;
    case GateType::kMosSwitch:
    case GateType::kEnableGate:
    case GateType::kPassEnSwitch:
      return count == 3;
    case GateType::kPassSwitch:
      return count == 2;
    case GateType::kPullGate:
      return count == 1;
    case GateType::kNInputGate:
    case GateType::kNOutputGate:
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
                 "instances in the same declaration",
                 Subclause("28.3.5"));
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
  Expect(TokenKind::kRParen, Subclause("28.3.6"));
  if (!ValidGateTerminalCount(kind, item->gate_terminals.size()))
    diag_.Error(loc, "incorrect number of terminals for gate instance",
                Subclause("28.3"));
  ValidateGateTerminalLvalues(kind, item->gate_terminals, diag_, loc);
  items.push_back(item);

  std::vector<std::string_view> array_names;
  while (Match(TokenKind::kComma)) {
    auto* next = ParseOneGateInstance(kind, loc);
    CheckGateArrayNameUnique(next, array_names, diag_);
    items.push_back(next);
  }
  Expect(TokenKind::kSemicolon, Subclause("28.3"));
}

ModuleItem* Parser::ParseOneGateInstance(GateKind kind, SourceLoc loc) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kGateInst;
  item->loc = loc;
  item->gate_kind = kind;

  // A.4.1.1's name_of_instance opens with an instance_identifier, which A.9.3
  // spells `simple_identifier | escaped_identifier`.
  ParseGateInstanceTail(*this, item, CheckIdentifier());
  if (!ValidGateTerminalCount(kind, item->gate_terminals.size()))
    diag_.Error(loc, "incorrect number of terminals for gate instance",
                Subclause("28.3"));
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
    Expect(TokenKind::kRParen, Subclause("28.16"));
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

// The strength value ParseStrength0 and ParseStrength1 give highz0 and highz1,
// the two keywords A.2.2.2 lists in drive_strength alone and in neither
// strength0 nor strength1.
constexpr uint8_t kHighzStrength = 1;

static void ValidateGateStrength(GateKind gate_kind, SourceLoc loc,
                                 uint8_t str0, uint8_t str1, DiagEngine& diag) {
  if (!GateAllowsStrength(gate_kind))
    diag.Error(loc, "drive strength not allowed on this gate type",
               Subclause("28.3.2"));

  // A.3.2 writes pullup_strength and pulldown_strength over strength0 and
  // strength1 alone, `( strength0 , strength1 )`, `( strength1 , strength0 )`
  // and the one keyword the gate drives with, where A.2.2.2's drive_strength
  // adds the four forms that pair highz0 or highz1 with the other; §28.10 has
  // the pull sources place "pull strength in the absence of a strength
  // specification", and a highz strength is no strength a source can place.
  if (GateTypeOf(gate_kind) == GateType::kPullGate &&
      (str0 == kHighzStrength || str1 == kHighzStrength))
    diag.Error(loc,
               "a pull source's strength is a strength0 or strength1 keyword; "
               "highz0 and highz1 are neither",
               Subclause("A.3.2"));

  if (gate_kind == GateKind::kPulldown && str0 == 0 && str1 != 0)
    diag.Error(loc, "pulldown single-strength must be a strength0 keyword",
               Subclause("28.3.2"));
  if (gate_kind == GateKind::kPullup && str1 == 0 && str0 != 0)
    diag.Error(loc, "pullup single-strength must be a strength1 keyword",
               Subclause("28.3.2"));

  if (GateAllowsStrength(gate_kind) && gate_kind != GateKind::kPullup &&
      gate_kind != GateKind::kPulldown && (str0 == 0 || str1 == 0))
    diag.Error(loc,
               "drive strength on this gate type requires both a "
               "strength0 and a strength1 keyword",
               Subclause("28.3.2"));
}

static void ValidateGateDelay(GateKind gate_kind, SourceLoc loc, Expr* delay,
                              Expr* delay_decay, DiagEngine& diag) {
  if (delay && !GateAllowsDelay(gate_kind))
    diag.Error(loc, "delay not allowed on this gate type", Subclause("28.3.3"));
  if (delay_decay && !GateUsesDelay3(gate_kind))
    diag.Error(loc, "this gate type allows at most 2 delay values",
               Subclause("28.3.3"));
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
    Expect(TokenKind::kRParen, Subclause("28.3.2"));
    ValidateGateStrength(gate_kind, loc, str0, str1, diag_);
  }

  Expr* delay = nullptr;
  Expr* delay_fall = nullptr;
  Expr* delay_decay = nullptr;
  ParseGateDelay(delay, delay_fall, delay_decay);
  ValidateGateDelay(gate_kind, loc, delay, delay_decay, diag_);

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
  Expect(TokenKind::kSemicolon, Subclause("28.3"));
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
    Expect(TokenKind::kComma, Subclause("28.3.2"));
    str1 = ParseStrength1();
  } else {
    str1 = ParseStrength1();
    Expect(TokenKind::kComma, Subclause("28.3.2"));
    str0 = ParseStrength0();
  }
  Expect(TokenKind::kRParen, Subclause("28.3.2"));

  if (str0 == 0 || str1 == 0) {
    diag_.Error(loc,
                "drive_strength on a UDP instance requires one strength0 "
                "keyword and one strength1 keyword",
                Subclause("28.3.2"));
  }
  return true;
}

}  // namespace delta
