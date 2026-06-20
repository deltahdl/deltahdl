#include "parser/parser.h"

namespace delta {

static void ExpectDeferredHashZero(DiagEngine& diag, const Token& tok) {
  if (tok.text != "0") {
    diag.Error(tok.loc, "deferred immediate assertion requires #0, got #" +
                            std::string(tok.text));
  }
}

static void SkipBalancedPropertySpec(Lexer& lexer) {
  int depth = 1;
  while (depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (lexer.Peek().Is(TokenKind::kLParen)) {
      ++depth;
    } else if (lexer.Peek().Is(TokenKind::kRParen)) {
      --depth;
      if (depth == 0) break;
    }
    lexer.Next();
  }
}

// Replicates Parser::Check against a Lexer so the free-function helpers see the
// same identifier/escaped-identifier folding the member helpers use.
static bool LexerCheck(Lexer& lexer, TokenKind kind) {
  auto cur = lexer.Peek().kind;
  if (kind == TokenKind::kIdentifier) {
    return cur == TokenKind::kIdentifier ||
           cur == TokenKind::kEscapedIdentifier;
  }
  return cur == kind;
}

// Cross-iteration state for the property-instance argument scan.
struct InstanceArgScanState {
  PropertyInstanceArgInfo info;
  int depth = 1;
  std::vector<std::string_view> cur_idents;
  int cur_tokens = 0;
  bool arg_has_content = false;
  std::string_view prev_ident;
  bool prev_was_ident = false;
};

static void FinalizeInstanceArg(InstanceArgScanState& st) {
  st.info.arg_idents.push_back(st.cur_idents);
  st.info.arg_is_single_ident.push_back(st.cur_tokens == 1 &&
                                        st.cur_idents.size() == 1);
  st.cur_idents.clear();
  st.cur_tokens = 0;
}

static void HandleInstanceArgLParen(Lexer& lexer, ModuleItem* item,
                                    InstanceArgScanState& st) {
  if (st.prev_was_ident) item->prop_instance_refs.push_back(st.prev_ident);
  lexer.Next();
  ++st.depth;
  ++st.cur_tokens;
  st.arg_has_content = true;
  st.prev_was_ident = false;
}

// Returns true when the matching ')' closing the whole list was consumed.
static bool HandleInstanceArgRParen(Lexer& lexer, InstanceArgScanState& st) {
  lexer.Next();
  --st.depth;
  if (st.depth == 0) {
    if (st.arg_has_content) FinalizeInstanceArg(st);
    return true;
  }
  ++st.cur_tokens;
  st.prev_was_ident = false;
  return false;
}

static void HandleInstanceArgComma(Lexer& lexer, InstanceArgScanState& st) {
  lexer.Next();
  FinalizeInstanceArg(st);
  st.arg_has_content = true;
  st.prev_was_ident = false;
}

static void HandleInstanceArgIdent(Lexer& lexer, InstanceArgScanState& st) {
  auto t = lexer.Next();
  st.cur_idents.push_back(t.text);
  ++st.cur_tokens;
  st.arg_has_content = true;
  st.prev_ident = t.text;
  st.prev_was_ident = true;
}

static void HandleInstanceArgOther(Lexer& lexer, InstanceArgScanState& st) {
  lexer.Next();
  ++st.cur_tokens;
  st.arg_has_content = true;
  st.prev_was_ident = false;
}

// §16.12.17 R4: capture the actual-argument shape of one property instance.
// Entry token is the opening '('; the matching ')' is consumed. Nested instance
// references are still recorded into prop_instance_refs.
static void CaptureInstanceArgs(Lexer& lexer, ModuleItem* item,
                                std::string_view callee) {
  InstanceArgScanState st;
  st.info.callee = callee;
  lexer.Next();  // '('
  while (st.depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (LexerCheck(lexer, TokenKind::kLParen)) {
      HandleInstanceArgLParen(lexer, item, st);
    } else if (LexerCheck(lexer, TokenKind::kRParen)) {
      if (HandleInstanceArgRParen(lexer, st)) break;
    } else if (st.depth == 1 && LexerCheck(lexer, TokenKind::kComma)) {
      HandleInstanceArgComma(lexer, st);
    } else if (LexerCheck(lexer, TokenKind::kIdentifier)) {
      HandleInstanceArgIdent(lexer, st);
    } else {
      HandleInstanceArgOther(lexer, st);
    }
  }
  item->prop_instance_args.push_back(std::move(st.info));
}

// §16.6/§16.10: a built-in type keyword that may head the var_data_type of an
// assertion_variable_declaration (the harvest only recognises built-in cases).
static bool IsBuiltinTypeKwForLocalVar(TokenKind k) {
  switch (k) {
    case TokenKind::kKwReg:
    case TokenKind::kKwLogic:
    case TokenKind::kKwBit:
    case TokenKind::kKwByte:
    case TokenKind::kKwShortint:
    case TokenKind::kKwInt:
    case TokenKind::kKwLongint:
    case TokenKind::kKwInteger:
    case TokenKind::kKwReal:
    case TokenKind::kKwShortreal:
    case TokenKind::kKwRealtime:
    case TokenKind::kKwTime:
    case TokenKind::kKwString:
    case TokenKind::kKwChandle:
      return true;
    default:
      return false;
  }
}

Stmt* Parser::ParseProceduralConcurrentAssertLike(StmtKind kind) {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = kind;
  stmt->range.start = CurrentLoc();

  stmt->is_procedural_concurrent = true;
  Expect(TokenKind::kKwProperty);
  Expect(TokenKind::kLParen);
  stmt->assert_expr = nullptr;
  SkipBalancedPropertySpec(lexer_);
  Expect(TokenKind::kRParen);

  if (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwElse)) {
    stmt->assert_pass_stmt = ParseStmt();
  }
  if (Match(TokenKind::kKwElse)) {
    stmt->assert_fail_stmt = ParseStmt();
  }
  if (!stmt->assert_pass_stmt && !stmt->assert_fail_stmt) {
    Expect(TokenKind::kSemicolon);
  }
  return stmt;
}

Stmt* Parser::ParseImmediateAssertLike(StmtKind kind, TokenKind keyword) {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = kind;
  stmt->range.start = CurrentLoc();
  Expect(keyword);

  if (Check(TokenKind::kKwProperty)) {
    return ParseProceduralConcurrentAssertLike(kind);
  }

  if (Match(TokenKind::kHash)) {
    auto tok = Expect(TokenKind::kIntLiteral);
    ExpectDeferredHashZero(diag_, tok);
    stmt->is_deferred = true;
  } else if (Match(TokenKind::kKwFinal)) {
    stmt->is_deferred = true;
    stmt->is_final_deferred = true;
  }

  Expect(TokenKind::kLParen);
  stmt->assert_expr = ParseExpr();
  Expect(TokenKind::kRParen);

  if (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwElse)) {
    stmt->assert_pass_stmt = ParseStmt();
  }
  if (Match(TokenKind::kKwElse)) {
    stmt->assert_fail_stmt = ParseStmt();
  }
  if (!stmt->assert_pass_stmt && !stmt->assert_fail_stmt) {
    Expect(TokenKind::kSemicolon);
  }

  return stmt;
}

Stmt* Parser::ParseImmediateAssert() {
  return ParseImmediateAssertLike(StmtKind::kAssertImmediate,
                                  TokenKind::kKwAssert);
}

Stmt* Parser::ParseImmediateAssume() {
  return ParseImmediateAssertLike(StmtKind::kAssumeImmediate,
                                  TokenKind::kKwAssume);
}

Stmt* Parser::ParseImmediateCover() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kCoverImmediate;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwCover);

  if (Check(TokenKind::kKwProperty)) {
    return ParseProceduralConcurrentAssertLike(StmtKind::kCoverImmediate);
  }

  if (Match(TokenKind::kHash)) {
    auto tok = Expect(TokenKind::kIntLiteral);
    ExpectDeferredHashZero(diag_, tok);
    stmt->is_deferred = true;
  } else if (Match(TokenKind::kKwFinal)) {
    stmt->is_deferred = true;
    stmt->is_final_deferred = true;
  }

  Expect(TokenKind::kLParen);
  stmt->assert_expr = ParseExpr();
  Expect(TokenKind::kRParen);

  if (!Check(TokenKind::kSemicolon)) {
    stmt->assert_pass_stmt = ParseStmt();
  } else {
    Expect(TokenKind::kSemicolon);
  }

  return stmt;
}

static Expr* SkipPropertySpec(Arena& arena, Lexer& lexer, SourceLoc loc) {
  int depth = 1;
  while (depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (lexer.Peek().Is(TokenKind::kLParen)) {
      ++depth;
    } else if (lexer.Peek().Is(TokenKind::kRParen)) {
      --depth;
      if (depth == 0) break;
    }
    lexer.Next();
  }
  auto* expr = arena.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->text = "<property_spec>";
  expr->range.start = loc;
  return expr;
}

static bool IsDeferredImmediate(Lexer& lexer) {
  if (lexer.Peek().Is(TokenKind::kHash)) return true;
  if (lexer.Peek().Is(TokenKind::kKwFinal)) return true;
  return false;
}

static ModuleItem* WrapStmtAsItem(Arena& arena, Stmt* stmt, SourceLoc loc) {
  auto* item = arena.Create<ModuleItem>();
  item->kind = ModuleItemKind::kAssertProperty;
  item->loc = loc;
  item->body = stmt;
  return item;
}

ModuleItem* Parser::ParseDeferredImmediateItem(SourceLoc loc, StmtKind kind) {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = kind;
  stmt->range.start = loc;
  stmt->is_deferred = true;
  if (Match(TokenKind::kHash)) {
    auto tok = Expect(TokenKind::kIntLiteral);

    ExpectDeferredHashZero(diag_, tok);
  } else if (Match(TokenKind::kKwFinal)) {
    stmt->is_final_deferred = true;
  }
  Expect(TokenKind::kLParen);
  stmt->assert_expr = ParseExpr();
  Expect(TokenKind::kRParen);
  if (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwElse)) {
    stmt->assert_pass_stmt = ParseStmt();
  }
  if (Match(TokenKind::kKwElse)) stmt->assert_fail_stmt = ParseStmt();
  if (!stmt->assert_pass_stmt && !stmt->assert_fail_stmt) {
    Expect(TokenKind::kSemicolon);
  }
  return WrapStmtAsItem(arena_, stmt, loc);
}

ModuleItem* Parser::ParsePropertyAssertLike(ModuleItemKind kind,
                                            TokenKind keyword) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = kind;
  item->loc = CurrentLoc();
  Expect(keyword);

  if (IsDeferredImmediate(lexer_)) {
    StmtKind sk = (kind == ModuleItemKind::kAssertProperty)
                      ? StmtKind::kAssertImmediate
                      : StmtKind::kAssumeImmediate;
    return ParseDeferredImmediateItem(item->loc, sk);
  }

  Expect(TokenKind::kKwProperty);
  Expect(TokenKind::kLParen);
  item->assert_expr = SkipPropertySpec(arena_, lexer_, CurrentLoc());
  Expect(TokenKind::kRParen);

  if (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwElse)) {
    item->assert_pass_stmt = ParseStmt();
  }
  if (Match(TokenKind::kKwElse)) {
    item->assert_fail_stmt = ParseStmt();
  }
  if (!item->assert_pass_stmt && !item->assert_fail_stmt) {
    Expect(TokenKind::kSemicolon);
  }
  return item;
}

ModuleItem* Parser::ParseAssertProperty() {
  return ParsePropertyAssertLike(ModuleItemKind::kAssertProperty,
                                 TokenKind::kKwAssert);
}

ModuleItem* Parser::ParseAssumeProperty() {
  return ParsePropertyAssertLike(ModuleItemKind::kAssumeProperty,
                                 TokenKind::kKwAssume);
}

ModuleItem* Parser::ParseCoverProperty() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kCoverProperty;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwCover);

  if (IsDeferredImmediate(lexer_)) {
    auto* stmt = arena_.Create<Stmt>();
    stmt->kind = StmtKind::kCoverImmediate;
    stmt->range.start = item->loc;
    stmt->is_deferred = true;
    if (Match(TokenKind::kHash)) {
      auto tok = Expect(TokenKind::kIntLiteral);

      ExpectDeferredHashZero(diag_, tok);
    } else if (Match(TokenKind::kKwFinal)) {
      stmt->is_final_deferred = true;
    }
    Expect(TokenKind::kLParen);
    stmt->assert_expr = ParseExpr();
    Expect(TokenKind::kRParen);
    if (!Check(TokenKind::kSemicolon)) {
      stmt->assert_pass_stmt = ParseStmt();
    } else {
      Expect(TokenKind::kSemicolon);
    }
    return WrapStmtAsItem(arena_, stmt, item->loc);
  }

  if (Check(TokenKind::kKwSequence)) {
    item->kind = ModuleItemKind::kCoverSequence;
    Expect(TokenKind::kKwSequence);
  } else {
    Expect(TokenKind::kKwProperty);
  }

  Expect(TokenKind::kLParen);
  item->assert_expr = SkipPropertySpec(arena_, lexer_, CurrentLoc());
  Expect(TokenKind::kRParen);

  if (!Check(TokenKind::kSemicolon)) {
    item->assert_pass_stmt = ParseStmt();
  } else {
    Expect(TokenKind::kSemicolon);
  }
  return item;
}

ModuleItem* Parser::ParseRestrictProperty() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kRestrictProperty;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwRestrict);
  Expect(TokenKind::kKwProperty);
  Expect(TokenKind::kLParen);
  item->assert_expr = SkipPropertySpec(arena_, lexer_, CurrentLoc());
  Expect(TokenKind::kRParen);
  Expect(TokenKind::kSemicolon);
  return item;
}

// Cross-iteration state for the named-property port-list scan. local_run:
// §16.12.19/§16.12.17 R4 `local` qualifies the comma-separated run of names
// until a fresh type specifier (not directly after `local`/`input`).
struct PropertyPortScanState {
  int depth = 1;
  bool expect_formal_name = true;
  bool saw_local = false;
  bool local_run = false;
  TokenKind prev_kind = TokenKind::kComma;
};

// Handles a type keyword in a property port; ends the local run unless directly
// after `local`/`input`. Consumes the token.
static void HandlePropertyPortTypeKw(Lexer& lexer, PropertyPortScanState& st) {
  if (st.prev_kind != TokenKind::kKwLocal &&
      st.prev_kind != TokenKind::kKwInput) {
    st.local_run = false;
  }
  lexer.Next();
}

// Handles output/inout/input in a property port (§16.12.19), consuming it.
static void HandlePropertyPortDirection(Lexer& lexer, DiagEngine& diag,
                                        PropertyPortScanState& st) {
  if (LexerCheck(lexer, TokenKind::kKwOutput) ||
      LexerCheck(lexer, TokenKind::kKwInout)) {
    // §16.12.19: a local variable formal of a named property must have
    // direction `input`; `inout`/`output` are illegal (A.2.10
    // property_lvar_port_direction admits only `input`).
    diag.Error(lexer.Peek().loc, "property port direction must be 'input'");
    lexer.Next();
    st.saw_local = false;
  } else {
    // `input` is permitted only after `local`.
    if (!st.saw_local) {
      diag.Error(lexer.Peek().loc,
                 "property port direction 'input' requires 'local'");
    }
    lexer.Next();
    st.saw_local = false;
  }
}

// Harvests a formal_port_identifier (rightmost id), recording local-run state.
static void HandlePropertyPortFormalName(Lexer& lexer, ModuleItem* item,
                                         PropertyPortScanState& st) {
  auto name_tok = lexer.Next();
  if (!LexerCheck(lexer, TokenKind::kComma) &&
      !LexerCheck(lexer, TokenKind::kRParen) &&
      !LexerCheck(lexer, TokenKind::kEq)) {
    if (LexerCheck(lexer, TokenKind::kIdentifier)) {
      name_tok = lexer.Next();
    }
  }
  item->prop_formals.push_back(name_tok.text);
  item->prop_formal_is_local.push_back(st.local_run);
  st.expect_formal_name = false;
  st.saw_local = false;
}

// §16.12 named-property port list: on entry '(' has been consumed; drains the
// formal list through ')', recording names/local qualification and §16.12.19.
static void ParsePropertyPortList(Lexer& lexer, DiagEngine& diag,
                                  ModuleItem* item) {
  PropertyPortScanState st;
  while (st.depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    TokenKind this_kind = lexer.Peek().kind;
    if (LexerCheck(lexer, TokenKind::kLParen)) {
      lexer.Next();
      ++st.depth;
    } else if (LexerCheck(lexer, TokenKind::kRParen)) {
      lexer.Next();
      --st.depth;
      if (st.depth == 0) break;
    } else if (st.depth == 1 && LexerCheck(lexer, TokenKind::kComma)) {
      lexer.Next();
      st.expect_formal_name = true;
      st.saw_local = false;
    } else if (st.depth == 1 && LexerCheck(lexer, TokenKind::kEq)) {
      lexer.Next();
      st.expect_formal_name = false;
    } else if (st.depth == 1 && LexerCheck(lexer, TokenKind::kKwLocal)) {
      lexer.Next();
      st.saw_local = true;
      st.local_run = true;
    } else if (st.depth == 1 && IsBuiltinTypeKwForLocalVar(lexer.Peek().kind)) {
      HandlePropertyPortTypeKw(lexer, st);
    } else if (st.depth == 1 && (LexerCheck(lexer, TokenKind::kKwOutput) ||
                                 LexerCheck(lexer, TokenKind::kKwInout) ||
                                 LexerCheck(lexer, TokenKind::kKwInput))) {
      HandlePropertyPortDirection(lexer, diag, st);
    } else if (st.expect_formal_name && st.depth == 1 &&
               LexerCheck(lexer, TokenKind::kIdentifier)) {
      HandlePropertyPortFormalName(lexer, item, st);
    } else {
      lexer.Next();
    }
    st.prev_kind = this_kind;
  }
}

// Handles the property-case bookkeeping tokens (case/endcase/default). Returns
// true when the token was one of these and has been consumed.
static bool ScanPropertyCaseToken(Lexer& lexer, DiagEngine& diag,
                                  std::vector<int>& case_default_counts) {
  if (LexerCheck(lexer, TokenKind::kKwCase)) {
    case_default_counts.push_back(0);
    lexer.Next();
    return true;
  }
  if (LexerCheck(lexer, TokenKind::kKwEndcase)) {
    if (!case_default_counts.empty()) case_default_counts.pop_back();
    lexer.Next();
    return true;
  }
  if (LexerCheck(lexer, TokenKind::kKwDefault) &&
      !case_default_counts.empty()) {
    // §16.12.16: more than one default in one property case statement is
    // illegal.
    auto default_loc = lexer.Peek().loc;
    if (++case_default_counts.back() == 2) {
      diag.Error(default_loc,
                 "property case statement shall have at most one 'default' "
                 "item");
    }
    lexer.Next();
    return true;
  }
  return false;
}

// Handles §16.12.17 property operators. Returns true if consumed.
// R1: not/s_nexttime/s_eventually/s_always (prefix) and s_until/s_until_with
// (infix) bind the next instance as an operand (s_nexttime also advances time).
static bool ScanPropertyOperatorToken(Lexer& lexer,
                                      bool& expect_negated_operand,
                                      bool& saw_time_advance) {
  if (LexerCheck(lexer, TokenKind::kKwNot) ||
      LexerCheck(lexer, TokenKind::kKwSNexttime) ||
      LexerCheck(lexer, TokenKind::kKwSEventually) ||
      LexerCheck(lexer, TokenKind::kKwSAlways) ||
      LexerCheck(lexer, TokenKind::kKwSUntil) ||
      LexerCheck(lexer, TokenKind::kKwSUntilWith)) {
    if (LexerCheck(lexer, TokenKind::kKwSNexttime)) saw_time_advance = true;
    expect_negated_operand = true;
    lexer.Next();
    return true;
  }
  // §16.12.17 R3: ##, |=> and (s_)nexttime advance time; |-> does not.
  if (LexerCheck(lexer, TokenKind::kHashHash) ||
      LexerCheck(lexer, TokenKind::kPipeEqGt) ||
      LexerCheck(lexer, TokenKind::kKwNexttime)) {
    saw_time_advance = true;
    lexer.Next();
    return true;
  }
  return false;
}

// Handles an identifier token: a following '(' marks a property instance whose
// args are captured; otherwise it is a bare identifier. Consumes the token.
static void ScanPropertyIdentToken(Lexer& lexer, ModuleItem* item,
                                   bool& expect_negated_operand,
                                   bool saw_time_advance) {
  auto tok = lexer.Next();
  if (LexerCheck(lexer, TokenKind::kLParen)) {
    item->prop_instance_refs.push_back(tok.text);
    if (expect_negated_operand) {
      item->prop_negated_instance_refs.push_back(tok.text);
    }
    if (tok.text == item->name && !saw_time_advance) {
      item->prop_has_untimed_self_recursion = true;
    }
    expect_negated_operand = false;
    CaptureInstanceArgs(lexer, item, tok.text);
  } else {
    // A bare identifier is not a property instance, so any pending negation
    // operand is a simple expression.
    expect_negated_operand = false;
  }
}

// Processes one token of the named-property body scan (var decls are harvested
// by the caller). Cross-iteration state is carried by reference.
static void ScanPropertyBodyToken(Lexer& lexer, DiagEngine& diag,
                                  ModuleItem* item,
                                  std::vector<int>& case_default_counts,
                                  bool& expect_negated_operand,
                                  bool& saw_time_advance) {
  if (LexerCheck(lexer, TokenKind::kKwDisable)) {
    lexer.Next();
    if (LexerCheck(lexer, TokenKind::kKwIff)) {
      lexer.Next();
      ++item->prop_disable_iff_count;
    }
    return;
  }
  if (ScanPropertyCaseToken(lexer, diag, case_default_counts)) return;
  if (ScanPropertyOperatorToken(lexer, expect_negated_operand,
                                saw_time_advance)) {
    return;
  }
  if (LexerCheck(lexer, TokenKind::kIdentifier)) {
    ScanPropertyIdentToken(lexer, item, expect_negated_operand,
                           saw_time_advance);
    return;
  }
  // Opening parentheses are skipped so a negation can still reach an instance
  // wrapped in parentheses; any other token ends a pending negation operand.
  if (!LexerCheck(lexer, TokenKind::kLParen)) expect_negated_operand = false;
  lexer.Next();
}

// §16.12 + §F.4.1: capture formal names, disable-iff count, and nested instance
// references for the rewriter.
ModuleItem* Parser::ParsePropertyDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kPropertyDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwProperty);
  item->name = Expect(TokenKind::kIdentifier).text;

  if (Match(TokenKind::kLParen)) {
    ParsePropertyPortList(lexer_, diag_, item);
  }

  Expect(TokenKind::kSemicolon);

  // §16.10 var decls are harvested first; §16.12.16 stacks open case
  // statements (at-most-one-default); §16.12.17 R1/R3 track negation operand
  // and a preceding time advance.
  bool in_decl_prefix = true;
  std::vector<int> case_default_counts;
  bool expect_negated_operand = false;
  bool saw_time_advance = false;

  while (!Check(TokenKind::kKwEndproperty) && !AtEnd()) {
    if (in_decl_prefix && IsBuiltinTypeKwForLocalVar(CurrentToken().kind)) {
      HarvestAssertionVariableDecl(item);
      continue;
    }
    in_decl_prefix = false;
    ScanPropertyBodyToken(lexer_, diag_, item, case_default_counts,
                          expect_negated_operand, saw_time_advance);
  }
  Expect(TokenKind::kKwEndproperty);
  MatchEndLabel(item->name);
  return item;
}

namespace {

// §16.7: parse a plain decimal token like "5". Sized/based literals return
// false; the caller leaves that validation to downstream stages.
bool TryParsePlainDecimal(std::string_view text, uint64_t& out) {
  if (text.empty()) return false;
  uint64_t v = 0;
  for (char c : text) {
    if (c < '0' || c > '9') return false;
    if (v > (UINT64_MAX - 9) / 10) return false;
    v = v * 10 + static_cast<uint64_t>(c - '0');
  }
  out = v;
  return true;
}

}  // namespace

void Parser::ValidateLiteralCycleDelayRange(SourceLoc range_loc) {
  // §16.7: only the literal `##[ [-]INTLIT : [-]INTLIT ]` form is checked here
  // (symbolic bounds are deferred). The window is peeked under SavePos so the
  // body loop still sees every token afterwards.
  if (!Check(TokenKind::kLBracket)) return;
  auto saved = lexer_.SavePos();
  Consume();  // [
  bool lo_negative = false;
  if (Check(TokenKind::kMinus)) {
    lo_negative = true;
    Consume();
  }
  if (!Check(TokenKind::kIntLiteral)) {
    lexer_.RestorePos(saved);
    return;
  }
  Token lo = Consume();
  if (!Check(TokenKind::kColon)) {
    lexer_.RestorePos(saved);
    return;
  }
  Consume();  // :
  bool hi_negative = false;
  if (Check(TokenKind::kMinus)) {
    hi_negative = true;
    Consume();
  }
  if (!Check(TokenKind::kIntLiteral)) {
    lexer_.RestorePos(saved);
    return;
  }
  Token hi = Consume();
  if (!Check(TokenKind::kRBracket)) {
    lexer_.RestorePos(saved);
    return;
  }
  lexer_.RestorePos(saved);

  uint64_t lo_mag = 0;
  uint64_t hi_mag = 0;
  if (!TryParsePlainDecimal(lo.text, lo_mag)) return;
  if (!TryParsePlainDecimal(hi.text, hi_mag)) return;

  // §16.7 S2: a literal lower or upper bound below zero is illegal.
  if (lo_negative || hi_negative) {
    diag_.Error(range_loc,
                "cycle-delay range bounds cannot be negative (§16.7)");
    return;
  }
  // §16.7 S6: the upper bound must be at least the lower bound.
  if (hi_mag < lo_mag) {
    diag_.Error(range_loc,
                "cycle-delay range upper bound must be at least the lower "
                "bound (§16.7)");
  }
}

// Consumes the var_data_type prefix: leading type keyword, signing, dims.
static void SkipAssertVarTypePrefix(Lexer& lexer) {
  lexer.Next();  // var_data_type's leading type keyword.
  while (LexerCheck(lexer, TokenKind::kKwSigned) ||
         LexerCheck(lexer, TokenKind::kKwUnsigned)) {
    lexer.Next();
  }
  while (LexerCheck(lexer, TokenKind::kLBracket)) {
    int b_depth = 1;
    lexer.Next();
    while (b_depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
      if (LexerCheck(lexer, TokenKind::kLBracket))
        ++b_depth;
      else if (LexerCheck(lexer, TokenKind::kRBracket))
        --b_depth;
      lexer.Next();
    }
  }
}

// Skips one variable_decl_assignment initializer, stopping at the top-level
// comma/semicolon (or an unbalanced closer). The '=' is already consumed.
static void SkipAssertVarInitExpr(Lexer& lexer) {
  int e_depth = 0;
  while (!lexer.Peek().Is(TokenKind::kEof)) {
    if (LexerCheck(lexer, TokenKind::kLParen) ||
        LexerCheck(lexer, TokenKind::kLBracket) ||
        LexerCheck(lexer, TokenKind::kLBrace)) {
      ++e_depth;
      lexer.Next();
    } else if (LexerCheck(lexer, TokenKind::kRParen) ||
               LexerCheck(lexer, TokenKind::kRBracket) ||
               LexerCheck(lexer, TokenKind::kRBrace)) {
      if (e_depth == 0) break;
      --e_depth;
      lexer.Next();
    } else if (e_depth == 0 && (LexerCheck(lexer, TokenKind::kComma) ||
                                LexerCheck(lexer, TokenKind::kSemicolon))) {
      break;
    } else {
      lexer.Next();
    }
  }
}

void Parser::HarvestAssertionVariableDecl(ModuleItem* item) {
  // §16.10 Syntax 16-13: assertion_variable_declaration ::= var_data_type
  // list_of_variable_decl_assignments ; — skip the type prefix, then walk the
  // comma-separated list of <identifier> [ = <expression> ] entries; each
  // identifier names a distinct local variable in the body.
  SkipAssertVarTypePrefix(lexer_);
  while (!Check(TokenKind::kSemicolon) && !AtEnd()) {
    if (Check(TokenKind::kIdentifier)) {
      auto tok = Consume();
      item->prop_seq_assert_vars.push_back(tok.text);
      if (Check(TokenKind::kEq)) {
        Consume();
        SkipAssertVarInitExpr(lexer_);
      }
      if (Check(TokenKind::kComma)) Consume();
    } else {
      Consume();
    }
  }
  if (Check(TokenKind::kSemicolon)) Consume();
}

// Cross-iteration state for the §16.8 sequence_port_list scan. item_* fields
// track the in-progress port item; see §16.8.2 for local/type/direction rules.
struct SequencePortScanState {
  int depth = 1;
  bool expect_formal_name = true;
  bool item_saw_local = false;
  bool item_local_explicit_here = false;
  bool item_saw_explicit_type = false;
  Direction item_dir = Direction::kInput;
  bool item_saw_eq = false;
  SourceLoc item_start;
};

// §16.8.2: emit local-formal diagnostics for the completed item, record dir.
static void FinalizeSequencePortItem(DiagEngine& diag, ModuleItem* item,
                                     SequencePortScanState& st) {
  if (!st.item_saw_local) return;
  if (st.item_local_explicit_here && !st.item_saw_explicit_type) {
    diag.Error(st.item_start,
               "a local variable formal argument requires an explicit "
               "type in its own port item (§16.8.2)");
  }
  if (st.item_saw_eq &&
      (st.item_dir == Direction::kInout || st.item_dir == Direction::kOutput)) {
    diag.Error(st.item_start,
               "default actual argument is illegal for a local "
               "variable formal argument of direction inout or "
               "output (§16.8.2)");
  }
  item->prop_seq_local_lvar_directions.push_back(st.item_dir);
}

// §16.8.2 carry-through after a comma: an identifier-only port item inherits
// local/dir/type from the prior explicit item; a fresh starter breaks the
// carry.
static void ResetSequencePortAfterComma(Lexer& lexer,
                                        SequencePortScanState& st) {
  bool next_is_fresh_starter = LexerCheck(lexer, TokenKind::kKwLocal) ||
                               LexerCheck(lexer, TokenKind::kKwInput) ||
                               LexerCheck(lexer, TokenKind::kKwOutput) ||
                               LexerCheck(lexer, TokenKind::kKwInout) ||
                               IsBuiltinTypeKwForLocalVar(lexer.Peek().kind);
  if (next_is_fresh_starter) {
    st.item_saw_local = false;
    st.item_dir = Direction::kInput;
  }
  st.item_local_explicit_here = false;
  st.item_saw_explicit_type = false;
  st.item_saw_eq = false;
  st.expect_formal_name = true;
}

// Handles a direction keyword (input/output/inout) in a sequence port item.
static void HandleSequencePortDirection(Lexer& lexer, DiagEngine& diag,
                                        SequencePortScanState& st) {
  auto dir_tok = lexer.Next();
  if (!st.item_saw_local) {
    diag.Error(dir_tok.loc,
               "sequence port direction requires the 'local' keyword "
               "(§16.8.2)");
  }
  if (dir_tok.kind == TokenKind::kKwInput) {
    st.item_dir = Direction::kInput;
  } else if (dir_tok.kind == TokenKind::kKwOutput) {
    st.item_dir = Direction::kOutput;
  } else {
    st.item_dir = Direction::kInout;
  }
}

// Harvests a formal_port_identifier chain (rightmost id; leading = type alias).
static void HandleSequencePortFormalName(Lexer& lexer, ModuleItem* item,
                                         SequencePortScanState& st) {
  auto name_tok = lexer.Next();
  while (LexerCheck(lexer, TokenKind::kIdentifier)) {
    name_tok = lexer.Next();
    st.item_saw_explicit_type = true;
  }
  item->prop_formals.push_back(name_tok.text);
  st.expect_formal_name = false;
}

// §16.8 sequence_port_list: '(' consumed; drains the list through ')'
// (§16.8.2).
static void ParseSequencePortList(Lexer& lexer, DiagEngine& diag,
                                  ModuleItem* item) {
  SequencePortScanState st;
  st.item_start = lexer.Peek().loc;
  while (st.depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (LexerCheck(lexer, TokenKind::kLParen)) {
      lexer.Next();
      ++st.depth;
    } else if (LexerCheck(lexer, TokenKind::kRParen)) {
      if (st.depth == 1) FinalizeSequencePortItem(diag, item, st);
      lexer.Next();
      --st.depth;
      if (st.depth == 0) break;
    } else if (st.depth == 1 && LexerCheck(lexer, TokenKind::kComma)) {
      FinalizeSequencePortItem(diag, item, st);
      lexer.Next();
      st.item_start = lexer.Peek().loc;
      ResetSequencePortAfterComma(lexer, st);
    } else if (st.depth == 1 && LexerCheck(lexer, TokenKind::kKwLocal)) {
      if (!st.item_saw_local) st.item_start = lexer.Peek().loc;
      st.item_saw_local = true;
      st.item_local_explicit_here = true;
      lexer.Next();
    } else if (st.depth == 1 && (LexerCheck(lexer, TokenKind::kKwInput) ||
                                 LexerCheck(lexer, TokenKind::kKwOutput) ||
                                 LexerCheck(lexer, TokenKind::kKwInout))) {
      HandleSequencePortDirection(lexer, diag, st);
    } else if (st.depth == 1 && IsBuiltinTypeKwForLocalVar(lexer.Peek().kind)) {
      lexer.Next();
      st.item_saw_explicit_type = true;
    } else if (st.depth == 1 && LexerCheck(lexer, TokenKind::kEq)) {
      st.item_saw_eq = true;
      lexer.Next();
      st.expect_formal_name = false;
    } else if (st.depth == 1 && st.expect_formal_name &&
               LexerCheck(lexer, TokenKind::kIdentifier)) {
      HandleSequencePortFormalName(lexer, item, st);
    } else {
      lexer.Next();
    }
  }
}

ModuleItem* Parser::ParseSequenceDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kSequenceDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwSequence);
  item->name = Expect(TokenKind::kIdentifier).text;

  // §16.8 sequence_port_list: harvest formal_port_identifier names (for
  // elaborator instance flattening/cycle detection) and police the §16.8.2
  // local-variable rules; see ParseSequencePortList.
  if (Match(TokenKind::kLParen)) {
    ParseSequencePortList(lexer_, diag_, item);
  }

  Expect(TokenKind::kSemicolon);

  // §16.10: harvest var decls at the head, then scan §16.8 instance refs.
  bool in_decl_prefix = true;
  while (!Check(TokenKind::kKwEndsequence) && !AtEnd()) {
    if (in_decl_prefix && IsBuiltinTypeKwForLocalVar(CurrentToken().kind)) {
      HarvestAssertionVariableDecl(item);
      continue;
    }
    in_decl_prefix = false;

    if (Check(TokenKind::kHashHash)) {
      auto delay_loc = CurrentLoc();
      Consume();
      ValidateLiteralCycleDelayRange(delay_loc);
      continue;
    }
    if (Check(TokenKind::kIdentifier)) {
      auto tok = Consume();
      item->prop_instance_refs.push_back(tok.text);
      continue;
    }
    Consume();
  }
  Expect(TokenKind::kKwEndsequence);
  MatchEndLabel(item->name);
  return item;
}

Stmt* Parser::ParseExpectStmt() {
  auto* stmt = arena_.Create<Stmt>();

  stmt->kind = StmtKind::kExpect;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwExpect);
  Expect(TokenKind::kLParen);

  int depth = 1;
  while (depth > 0 && !AtEnd()) {
    if (Match(TokenKind::kLParen)) {
      ++depth;
    } else if (Match(TokenKind::kRParen)) {
      --depth;
    } else {
      Consume();
    }
  }

  if (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwElse)) {
    stmt->assert_pass_stmt = ParseStmt();
  }
  if (Match(TokenKind::kKwElse)) stmt->assert_fail_stmt = ParseStmt();
  if (!stmt->assert_pass_stmt && !stmt->assert_fail_stmt) {
    Expect(TokenKind::kSemicolon);
  }
  stmt->range.end = CurrentLoc();
  return stmt;
}

}  // namespace delta
