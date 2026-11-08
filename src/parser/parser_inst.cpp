#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"
#include "parser/parser_token_skips.h"

namespace delta {

namespace {

void RecordInstRange(ModuleItem* item) {
  if (item->inst_dims.empty()) return;
  item->inst_range_left = item->inst_dims[0].first;
  item->inst_range_right = item->inst_dims[0].second;
}

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

void PublishInstances(std::vector<ModuleItem*>* extra_items,
                      const std::vector<ModuleItem*>& instances) {
  if (!extra_items) return;
  extra_items->insert(extra_items->end(), instances.begin(), instances.end());
}

}  // namespace

bool Parser::AtCheckerInstantiationStmt() {
  if (!CheckIdentifier()) return false;
  auto saved = lexer_.SavePos();
  Consume();
  if (Match(TokenKind::kColonColon) && CheckIdentifier()) Consume();
  bool is_inst = LooksLikeScopedInstTail();
  lexer_.RestorePos(saved);
  return is_inst;
}

Stmt* Parser::ParseCheckerInstantiationStmt() {
  SourceLoc loc = CurrentLoc();
  if (always_or_initial_depth_ == 0) {
    diag_.Error(loc,
                "a checker instantiation in procedural code shall be in an "
                "always or an initial procedure",
                Subclause("17.3"));
  }
  std::vector<ModuleItem*> items;
  auto name_tok = Consume();
  if (Check(TokenKind::kColonColon)) {
    ParseScopedTypeOrInst(name_tok, items);
  } else {
    ParseModuleInstList(name_tok, &items);
  }
  std::vector<Stmt*> stmts;
  for (ModuleItem* item : items) {
    item->inst_in_procedure = true;
    auto* stmt = arena_.Create<Stmt>();
    stmt->kind = StmtKind::kCheckerInstantiation;
    stmt->range.start = item->loc;
    stmt->decl_item = item;
    stmts.push_back(stmt);
  }
  if (stmts.size() == 1) return stmts.front();
  auto* block = arena_.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->range.start = loc;
  block->stmts = std::move(stmts);
  return block;
}

ModuleItem* Parser::ParseModuleInst(const Token& module_tok) {
  return ParseModuleInstList(module_tok, nullptr);
}

ModuleItem* Parser::ParseModuleInstList(const Token& module_tok,
                                        std::vector<ModuleItem*>* extra_items) {
  std::vector<std::pair<std::string_view, Expr*>> params;
  const bool kParamsWritten = Match(TokenKind::kHash);
  if (kParamsWritten) ParseParamValueAssignment(params);

  auto parse_inst_dims = [&](ModuleItem* item) {
    while (Match(TokenKind::kLBracket)) {
      Expr* left = ParseExpr();
      Expr* right = Match(TokenKind::kColon) ? ParseExpr() : nullptr;
      Expect(TokenKind::kRBracket, Subclause("23.3.2"));
      item->inst_dims.push_back({left, right});
    }
  };

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

  auto parse_inst_port_list = [&](ModuleItem* item) {
    Expect(TokenKind::kLParen, Subclause("23.3.2"));
    if (Check(TokenKind::kRParen)) return;
    bool named = ParsePortConnection(item);
    bool mixed = false;
    while (Match(TokenKind::kComma)) parse_next_port(item, named, mixed);
  };

  auto parse_one_instance = [&]() -> ModuleItem* {
    auto* item = MakeInstanceItem(arena_, module_tok, params);
    item->inst_param_assignment_written = kParamsWritten;
    item->inst_name = ExpectIdentifier(Subclause("23.3.2")).text;
    parse_inst_dims(item);
    RecordInstRange(item);
    parse_inst_port_list(item);
    Expect(TokenKind::kRParen, Subclause("23.3.2"));
    return item;
  };

  std::vector<ModuleItem*> instances;
  do {
    instances.push_back(parse_one_instance());
    instances.back()->inst_continues_list = instances.size() > 1;
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
      expr = ParseTypeOr(&Parser::ParseMinTypMaxExpr);
    }
    Expect(TokenKind::kRParen, Subclause("23.10.2.2"));
    out.push_back({name.text, expr});
    return true;
  }
  out.push_back({{}, ParseTypeOr(&Parser::ParseMinTypMaxExpr)});
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

Expr* Parser::ParsePortActual() {
  auto saved = lexer_.SavePos();
  uint32_t errors = diag_.SuppressedErrorCount();
  diag_.PushSuppress();
  bool plain = true;
  Expr* actual =
      ParserPropertySpecHelpers::ParsePropertyActualArg(*this, plain);
  bool read = !plain && actual != nullptr &&
              (Check(TokenKind::kComma) || Check(TokenKind::kRParen)) &&
              (actual->property_actual != nullptr ||
               errors == diag_.SuppressedErrorCount());
  diag_.PopSuppress();
  if (read) return actual;
  lexer_.RestorePos(saved);
  return ParseExpr();
}

bool Parser::ParsePortConnection(ModuleItem* item) {
  auto attrs = ParseAttributes();
  if (!attrs.empty()) item->inst_port_attr_loc = attrs.front().loc;
  if (Check(TokenKind::kDotStar)) {
    auto loc = CurrentLoc();
    Consume();
    if (item->inst_wildcard) {
      diag_.Error(loc,
                  ".* already appears earlier in this port connection list",
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
        expr = ParsePortActual();
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
    item->inst_ports.push_back({{}, ParsePortActual()});
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

void Parser::ReportDriveStrengthAfterDelay(const Expr* delay,
                                           std::string_view subclause) {
  if (delay == nullptr || !Check(TokenKind::kLParen)) {
    return;
  }
  auto saved = lexer_.SavePos();
  auto loc = CurrentLoc();
  Consume();
  if (!IsDriveStrengthToken(CurrentToken().kind)) {
    lexer_.RestorePos(saved);
    return;
  }
  diag_.Error(loc,
              "the drive strength comes after the delay here; it has to be "
              "written first",
              Subclause(subclause));
  uint8_t s0 = 0, s1 = 0;
  ParseDriveStrength(s0, s1);
  Expect(TokenKind::kRParen, Subclause(subclause));
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

static void ReportNullProcedureBody(const Stmt* body, SourceLoc loc,
                                    std::string_view procedure,
                                    DiagEngine& diag) {
  if (body->kind != StmtKind::kNull) return;
  diag.Error(loc,
             std::format("{} procedure's body is a statement, which cannot be "
                         "null",
                         procedure),
             Subclause("A.6.2"));
}

ModuleItem* Parser::ParseAlwaysBlock(AlwaysKind kind) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = AlwaysKindToItemKind(kind);
  item->always_kind = kind;
  item->loc = CurrentLoc();
  Consume();
  struct DepthGuard {
    int& d;
    explicit DepthGuard(int& d) : d(d) { ++d; }
    ~DepthGuard() { --d; }
  } guard(always_or_initial_depth_);

  if (kind == AlwaysKind::kAlways) {
    ModuleItem* statement =
        ParserPropertySpecHelpers::TryParseAlwaysConcurrentAssertion(*this);
    if (statement != nullptr) return statement;
  }

  bool has_event_control = Check(TokenKind::kAt);
  if (has_event_control) {
    auto saved = lexer_.SavePos();
    Consume();
    if (!Check(TokenKind::kStar) && !Check(TokenKind::kLParen)) {
      lexer_.RestorePos(saved);
      Stmt* control = ParseEventControlStmt();
      item->sensitivity = std::move(control->events);
      item->body = control->body;
      return item;
    }
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

  SourceLoc body_loc = CurrentLoc();
  item->body = ParseStmt();
  if (!has_event_control) {
    ReportNullProcedureBody(item->body, body_loc, "an always", diag_);
  }
  return item;
}

ModuleItem* Parser::ParseInitialBlock() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kInitialBlock;
  item->loc = CurrentLoc();
  Consume();
  struct DepthGuard {
    int& d;
    explicit DepthGuard(int& d) : d(d) { ++d; }
    ~DepthGuard() { --d; }
  } guard(always_or_initial_depth_);
  item->body = ParseStmt();
  return item;
}

ModuleItem* Parser::ParseFinalBlock() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kFinalBlock;
  item->loc = CurrentLoc();
  Consume();
  SourceLoc body_loc = CurrentLoc();
  item->body = ParseStmt();
  ReportNullProcedureBody(item->body, body_loc, "a final", diag_);
  return item;
}

bool Parser::TryTakeIllFormedSimpleIdentifier(Token* out) {
  auto tok = CurrentToken();
  if (tok.Is(TokenKind::kSystemIdentifier)) {
    diag_.Error(
        tok.loc,
        "identifier '" + std::string(tok.text) + "' shall not begin with '$'",
        Subclause("5.6"));
    *out = Consume();
    out->kind = TokenKind::kIdentifier;
    return true;
  }
  if (!tok.Is(TokenKind::kIntLiteral) ||
      !std::ranges::all_of(tok.text, [](char c) {
        return std::isdigit(static_cast<unsigned char>(c)) != 0 || c == '_';
      })) {
    return false;
  }
  auto saved = lexer_.SavePos();
  Consume();
  auto next = CurrentToken();
  if (!next.Is(TokenKind::kIdentifier) || !TokenFollowsDirectly(tok, next)) {
    lexer_.RestorePos(saved);
    return false;
  }
  Consume();
  *out = tok;
  out->kind = TokenKind::kIdentifier;
  out->text =
      std::string_view(tok.text.data(), tok.text.size() + next.text.size());
  diag_.Error(tok.loc,
              "identifier '" + std::string(out->text) +
                  "' shall not begin with a digit",
              Subclause("5.6"));
  return true;
}

Token Parser::ExpectIdentifier(Subclause subclause) {
  if (CheckIdentifier()) {
    return Consume();
  }
  Token ill_formed;
  if (TryTakeIllFormedSimpleIdentifier(&ill_formed)) {
    return ill_formed;
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
