#include <format>

#include "parser/parser.h"

namespace delta {

namespace {

// Record the leading instance dimension of `item` as its instance range. This
// is pure AST manipulation over an already-parsed instance, so it lives outside
// the parser proper to keep ParseModuleInstList readable.
void RecordInstRange(ModuleItem* item) {
  if (item->inst_dims.empty()) return;
  item->inst_range_left = item->inst_dims[0].first;
  item->inst_range_right = item->inst_dims[0].second;
}

// Allocate and seed the shared (non-name) fields of one module instance. These
// fields are pure AST data copied from the surrounding instantiation header, so
// the construction lives outside the parser proper. The caller fills in the
// instance name and the parsed dimensions/ports.
ModuleItem* MakeInstanceItem(
    Arena& arena, const Token& module_tok,
    const std::vector<std::pair<std::string_view, Expr*>>& params) {
  auto* item = arena.Create<ModuleItem>();
  item->kind = ModuleItemKind::kModuleInst;
  item->loc = module_tok.loc;
  item->inst_module = module_tok.text;
  item->inst_params = params;
  return item;
}

// Publish the fully parsed instance list to the caller's overflow vector when
// one was supplied. Pure container manipulation, kept out of the parser proper.
void PublishInstances(std::vector<ModuleItem*>* extra_items,
                      const std::vector<ModuleItem*>& instances) {
  if (!extra_items) return;
  extra_items->insert(extra_items->end(), instances.begin(), instances.end());
}

}  // namespace

ModuleItem* Parser::ParseModuleInst(const Token& module_tok) {
  return ParseModuleInstList(module_tok, nullptr);
}

ModuleItem* Parser::ParseModuleInstList(const Token& module_tok,
                                        std::vector<ModuleItem*>* extra_items) {
  std::vector<std::pair<std::string_view, Expr*>> params;
  if (Match(TokenKind::kHash)) {
    ParseParamValueAssignment(params);
  }

  // Parse the instance dimensions `( [ expr ( : expr )? ] )*` into `item`.
  auto parse_inst_dims = [&](ModuleItem* item) {
    while (Match(TokenKind::kLBracket)) {
      Expr* left = ParseExpr();
      Expr* right = Match(TokenKind::kColon) ? ParseExpr() : nullptr;
      Expect(TokenKind::kRBracket, Subclause("23.3.2"));
      item->inst_dims.push_back({left, right});
    }
  };

  // Parse one trailing port connection, diagnosing a named/ordered mix once.
  auto parse_next_port = [&](ModuleItem* item, bool named, bool& mixed) {
    auto conn_loc = CurrentLoc();
    bool inconsistent = ParsePortConnection(item) != named && !mixed;
    if (inconsistent) {
      diag_.Error(conn_loc,
                  "ordered and named port connections cannot be mixed",
                  Subclause("23.3.2"));
      mixed = true;
    }
  };

  // Parse the parenthesized port connection list into `item`.
  auto parse_inst_port_list = [&](ModuleItem* item) {
    Expect(TokenKind::kLParen, Subclause("23.3.2"));
    if (Check(TokenKind::kRParen)) return;
    bool named = ParsePortConnection(item);
    bool mixed = false;
    while (Match(TokenKind::kComma)) parse_next_port(item, named, mixed);
  };

  auto parse_one_instance = [&]() -> ModuleItem* {
    auto* item = MakeInstanceItem(arena_, module_tok, params);
    item->inst_name = Expect(TokenKind::kIdentifier, Subclause("23.3.2")).text;
    parse_inst_dims(item);
    RecordInstRange(item);
    parse_inst_port_list(item);
    Expect(TokenKind::kRParen, Subclause("23.3.2"));
    return item;
  };

  std::vector<ModuleItem*> instances;
  do {
    instances.push_back(parse_one_instance());
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon, Subclause("23.3.2"));
  PublishInstances(extra_items, instances);
  return instances.front();
}

void Parser::ParseParenList(std::vector<Expr*>& out) {
  Expect(TokenKind::kLParen, Subclause("13.5"));
  if (!Check(TokenKind::kRParen)) {
    out.push_back(ParseExpr());
    while (Match(TokenKind::kComma)) {
      out.push_back(ParseExpr());
    }
  }
  Expect(TokenKind::kRParen, Subclause("13.5"));
}

bool Parser::ParseParamValueEntry(
    std::vector<std::pair<std::string_view, Expr*>>& out) {
  if (Match(TokenKind::kDot)) {
    auto name = Expect(TokenKind::kIdentifier, Subclause("23.10.2.2"));
    Expect(TokenKind::kLParen, Subclause("23.10.2.2"));
    Expr* expr = nullptr;
    if (!Check(TokenKind::kRParen)) {
      expr = ParseExpr();
    }
    Expect(TokenKind::kRParen, Subclause("23.10.2.2"));
    out.push_back({name.text, expr});
    return true;
  }
  out.push_back({{}, ParseExpr()});
  return false;
}

void Parser::ParseParamValueAssignment(
    std::vector<std::pair<std::string_view, Expr*>>& out) {
  size_t start = out.size();
  std::vector<SourceLoc> entry_locs;
  Expect(TokenKind::kLParen, Subclause("23.10.2"));
  if (!Check(TokenKind::kRParen)) {
    entry_locs.push_back(CurrentLoc());
    bool named = ParseParamValueEntry(out);
    bool mixed = false;
    while (Match(TokenKind::kComma)) {
      auto entry_loc = CurrentLoc();
      entry_locs.push_back(entry_loc);
      bool next_named = ParseParamValueEntry(out);
      if (!mixed && next_named != named) {
        diag_.Error(
            entry_loc,
            "ordered and named parameter value assignments cannot be mixed",
            Subclause("23.3.2"));
        mixed = true;
      }
    }
  }
  Expect(TokenKind::kRParen, Subclause("23.10.2"));
  for (size_t i = 0; i < entry_locs.size(); ++i) {
    auto name = out[start + i].first;
    if (name.empty()) continue;
    for (size_t j = i + 1; j < entry_locs.size(); ++j) {
      if (out[start + j].first == name) {
        diag_.Error(
            entry_locs[j],
            std::format("duplicate parameter name '{}' in parameter value "
                        "assignment",
                        name),
            Subclause("23.10.2.2"));
        break;
      }
    }
  }
}

bool Parser::ParsePortConnection(ModuleItem* item) {
  ParseAttributes();
  if (Check(TokenKind::kDotStar)) {
    auto loc = CurrentLoc();
    Consume();
    if (item->inst_wildcard) {
      diag_.Error(loc,
                  ".* port connection shall appear at most once in a "
                  "port connection list",
                  Subclause("23.3.2"));
    }
    item->inst_wildcard = true;
    return true;
  }
  if (Match(TokenKind::kDot)) {
    auto name = Expect(TokenKind::kIdentifier, Subclause("23.3.2.2"));

    if (Match(TokenKind::kLParen)) {
      Expr* expr = nullptr;
      if (!Check(TokenKind::kRParen)) {
        expr = ParseExpr();
      }
      Expect(TokenKind::kRParen, Subclause("23.3.2.2"));
      item->inst_ports.push_back({name.text, expr});
      item->inst_ports_implicit.push_back(false);
    } else {
      auto* expr = arena_.Create<Expr>();
      expr->kind = ExprKind::kIdentifier;
      expr->text = name.text;
      expr->range.start = name.loc;
      item->inst_ports.push_back({name.text, expr});
      item->inst_ports_implicit.push_back(true);
    }
    return true;
  }

  if (Check(TokenKind::kComma) || Check(TokenKind::kRParen)) {
    item->inst_ports.push_back({{}, nullptr});
    item->inst_ports_implicit.push_back(false);
  } else {
    item->inst_ports.push_back({{}, ParseExpr()});
    item->inst_ports_implicit.push_back(false);
  }
  return false;
}

static bool IsStr0Token(TokenKind k) {
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

void Parser::ParseDriveStrength(uint8_t& s0, uint8_t& s1) {
  auto loc = CurrentLoc();
  if (IsStr0Token(CurrentToken().kind)) {
    s0 = ParseStrength0();
    Expect(TokenKind::kComma, Subclause("10.3.4"));
    s1 = ParseStrength1();
  } else {
    s1 = ParseStrength1();
    Expect(TokenKind::kComma, Subclause("10.3.4"));
    s0 = ParseStrength0();
  }

  if (s0 == 0 || s1 == 0) {
    diag_.Error(loc,
                "drive_strength on a continuous assignment requires one "
                "strength0 keyword and one strength1 keyword",
                Subclause("10.3.4"));
  }
}

static bool IsDriveStrengthToken(TokenKind k) {
  switch (k) {
    case TokenKind::kKwSupply0:
    case TokenKind::kKwStrong0:
    case TokenKind::kKwPull0:
    case TokenKind::kKwWeak0:
    case TokenKind::kKwHighz0:
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

// Report a drive strength written after the delay, given a parser positioned
// where the delay ended and `delay` holding whatever the delay parse produced.
// §10.3.4 rules that the strength specification "shall immediately follow the
// keyword (either the keyword for the net type or `assign`) and precede any
// delay specified", and the grammar writes that order into both constructs the
// sentence names: `continuous_assign ::= assign [ drive_strength ] [ delay3 ]
// list_of_net_assignments ;` in §A.6.1, and `net_declaration ::= net_type
// [ drive_strength | charge_strength ] [ vectored | scalared ]
// data_type_or_implicit [ delay3 ] list_of_net_decl_assignments ;` in §A.2.1.3.
// A parenthesis opening a strength at this point therefore stands after the
// delay, whichever of the two keywords began the construct.
//
// A null `delay` means no delay was written, so nothing here is out of order
// and the parenthesis belongs to whatever follows.
//
// The misplaced specification is consumed rather than left where it stands, so
// that the rest of the construct still parses and the run names §10.3.4 once
// instead of reporting the strength keyword as a missing expression or the
// parenthesis as a missing net name. Nothing records it: §10.3.4 gives a
// strength in this position no meaning to record.
void Parser::ReportDriveStrengthAfterDelay(const Expr* delay) {
  if (delay == nullptr || !Check(TokenKind::kLParen)) {
    return;
  }
  auto saved = lexer_.SavePos();
  auto loc = CurrentLoc();
  Consume();
  if (!IsDriveStrengthToken(CurrentToken().kind)) {
    // A parenthesis after a delay can legitimately open an assignment target,
    // so the parser has to see this one again.
    lexer_.RestorePos(saved);
    return;
  }
  diag_.Error(loc, "drive strength shall precede any delay specified",
              Subclause("10.3.4"));
  uint8_t s0 = 0, s1 = 0;
  ParseDriveStrength(s0, s1);
  Expect(TokenKind::kRParen, Subclause("10.3.4"));
}

void Parser::ParseContinuousAssign(std::vector<ModuleItem*>& items) {
  auto loc = CurrentLoc();
  Expect(TokenKind::kKwAssign, Subclause("10.3"));

  uint8_t ds0 = 0, ds1 = 0;
  if (Check(TokenKind::kLParen)) {
    auto saved = lexer_.SavePos();
    Consume();
    if (IsDriveStrengthToken(CurrentToken().kind)) {
      ParseDriveStrength(ds0, ds1);
      Expect(TokenKind::kRParen, Subclause("10.3.4"));
    } else {
      lexer_.RestorePos(saved);
    }
  }

  Expr* delay = nullptr;
  Expr* delay_fall = nullptr;
  Expr* delay_decay = nullptr;
  ParseGateDelay(delay, delay_fall, delay_decay);
  ReportDriveStrengthAfterDelay(delay);

  do {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kContAssign;
    item->loc = loc;
    item->drive_strength0 = ds0;
    item->drive_strength1 = ds1;
    item->assign_delay = delay;
    item->assign_delay_fall = delay_fall;
    item->assign_delay_decay = delay_decay;
    item->assign_lhs = ParseExpr();
    Expect(TokenKind::kEq, Subclause("10.3"));
    item->assign_rhs = ParseExpr();
    items.push_back(item);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon, Subclause("10.3"));
}

ModuleItem* Parser::ParseAlias() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kAlias;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwAlias, Subclause("10.11"));
  item->alias_nets.push_back(ParseExpr());
  // The grammar makes the first `=` and second net_lvalue mandatory; only
  // further pairings are part of the optional repetition.
  Expect(TokenKind::kEq, Subclause("10.11"));
  item->alias_nets.push_back(ParseExpr());
  while (Match(TokenKind::kEq)) {
    item->alias_nets.push_back(ParseExpr());
  }
  Expect(TokenKind::kSemicolon, Subclause("10.11"));
  return item;
}

static ModuleItemKind AlwaysKindToItemKind(AlwaysKind kind) {
  switch (kind) {
    case AlwaysKind::kAlways:
      return ModuleItemKind::kAlwaysBlock;
    case AlwaysKind::kAlwaysComb:
      return ModuleItemKind::kAlwaysCombBlock;
    case AlwaysKind::kAlwaysFF:
      return ModuleItemKind::kAlwaysFFBlock;
    case AlwaysKind::kAlwaysLatch:
      return ModuleItemKind::kAlwaysLatchBlock;
  }
  return ModuleItemKind::kAlwaysBlock;
}

ModuleItem* Parser::ParseAlwaysBlock(AlwaysKind kind) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = AlwaysKindToItemKind(kind);
  item->always_kind = kind;
  item->loc = CurrentLoc();
  Consume();

  if (Check(TokenKind::kAt)) {
    Consume();
    if (Match(TokenKind::kStar)) {
      item->is_star_sensitivity = true;
    } else if (Check(TokenKind::kLParen)) {
      Consume();
      if (Match(TokenKind::kStar)) {
        item->is_star_sensitivity = true;
      } else {
        item->sensitivity = ParseEventList();
      }
      Expect(TokenKind::kRParen, Subclause("9.4.2"));
    }
  }

  item->body = ParseStmt();
  return item;
}

ModuleItem* Parser::ParseInitialBlock() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kInitialBlock;
  item->loc = CurrentLoc();
  Consume();
  item->body = ParseStmt();
  return item;
}

ModuleItem* Parser::ParseFinalBlock() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kFinalBlock;
  item->loc = CurrentLoc();
  Consume();
  item->body = ParseStmt();
  return item;
}

Token Parser::ExpectIdentifier(Subclause subclause) {
  if (CheckIdentifier()) {
    return Consume();
  }
  auto tok = CurrentToken();
  diag_.Error(
      tok.loc,
      "expected identifier, got " + std::string(TokenKindName(tok.kind)),
      subclause);
  return tok;
}

void Parser::MatchEndLabel(std::string_view name) {
  if (Match(TokenKind::kColon)) {
    auto end_id = ExpectIdentifier(Subclause("9.3.4"));
    if (!name.empty() && end_id.text != name) {
      diag_.Error(end_id.loc,
                  "end label '" + std::string(end_id.text) +
                      "' does not match '" + std::string(name) + "'",
                  Subclause("9.3.4"));
    }
  }
}

bool Parser::CheckIdentifier() {
  return Check(TokenKind::kIdentifier) || Check(TokenKind::kEscapedIdentifier);
}

}  // namespace delta
