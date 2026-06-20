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

// §16.6/§16.10: a built-in scalar/integral/string type keyword that may head
// the var_data_type of an assertion_variable_declaration. User-defined type
// aliases also satisfy the grammar, but the parser's best-effort harvest only
// needs to recognise the built-in cases.
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

// §16.12 + §F.4.1: capture formal names, body disable-iff count, and nested
// property/sequence instance references so the rewriter has what it needs.
ModuleItem* Parser::ParsePropertyDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kPropertyDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwProperty);
  item->name = Expect(TokenKind::kIdentifier).text;

  if (Match(TokenKind::kLParen)) {
    int depth = 1;
    bool expect_formal_name = true;
    bool saw_local = false;
    // §16.12.19 / §16.12.17 Restriction 4: track whether the current formal was
    // declared as a local variable formal argument. `local` qualifies the whole
    // comma-separated run of names until a fresh type specifier (not directly
    // following `local`/`input`) begins a new, unqualified item.
    bool local_run = false;
    TokenKind prev_kind = TokenKind::kComma;
    while (depth > 0 && !AtEnd()) {
      TokenKind this_kind = CurrentToken().kind;
      if (Check(TokenKind::kLParen)) {
        Consume();
        ++depth;
      } else if (Check(TokenKind::kRParen)) {
        Consume();
        --depth;
        if (depth == 0) break;
      } else if (depth == 1 && Check(TokenKind::kComma)) {
        Consume();
        expect_formal_name = true;
        saw_local = false;
      } else if (depth == 1 && Check(TokenKind::kEq)) {
        Consume();
        expect_formal_name = false;
      } else if (depth == 1 && Check(TokenKind::kKwLocal)) {
        Consume();
        saw_local = true;
        local_run = true;
      } else if (depth == 1 &&
                 IsBuiltinTypeKwForLocalVar(CurrentToken().kind)) {
        // A built-in type keyword that does not directly follow `local` or
        // `input` starts a fresh formal item whose qualifiers do not include
        // `local`, so the local-variable run ends here.
        if (prev_kind != TokenKind::kKwLocal &&
            prev_kind != TokenKind::kKwInput) {
          local_run = false;
        }
        Consume();
      } else if (depth == 1 &&
                 (Check(TokenKind::kKwOutput) || Check(TokenKind::kKwInout))) {
        // §16.12.19: a local variable formal argument of a named property
        // shall have direction `input`; declaring one with direction `inout`
        // or `output` is illegal. The borrowed A.2.10 production
        // property_lvar_port_direction admits only `input`, so `output` and
        // `inout` have no legal role inside a property port, with or without a
        // preceding `local`.
        diag_.Error(CurrentLoc(), "property port direction must be 'input'");
        Consume();
        saw_local = false;
      } else if (depth == 1 && Check(TokenKind::kKwInput)) {
        // `input` is permitted only after `local`.
        if (!saw_local) {
          diag_.Error(CurrentLoc(),
                      "property port direction 'input' requires 'local'");
        }
        Consume();
        saw_local = false;
      } else if (expect_formal_name && depth == 1 &&
                 Check(TokenKind::kIdentifier)) {
        auto name_tok = Consume();
        if (!Check(TokenKind::kComma) && !Check(TokenKind::kRParen) &&
            !Check(TokenKind::kEq)) {
          if (Check(TokenKind::kIdentifier)) {
            name_tok = Consume();
          }
        }
        item->prop_formals.push_back(name_tok.text);
        item->prop_formal_is_local.push_back(local_run);
        expect_formal_name = false;
        saw_local = false;
      } else {
        Consume();
      }
      prev_kind = this_kind;
    }
  }

  Expect(TokenKind::kSemicolon);

  // §16.10: assertion_variable_declarations may appear at the head of a
  // property body, just as in a sequence body. Harvest them before the
  // body skip loop falls through to its existing instance-reference scan.
  bool in_decl_prefix = true;
  // §16.12.16: track open case property statements so the optional default item
  // can be policed. Each entry counts the default items seen in the
  // corresponding `case`..`endcase`; nested case statements stack, so an inner
  // default is never charged against an outer case.
  std::vector<int> case_default_counts;
  // §16.12.17 Restriction 1: when a prefix property-negation/strong operator is
  // seen, the next property instance reached (possibly through opening parens)
  // is its operand and is recorded so the elaborator can forbid negating a
  // recursive property.
  bool expect_negated_operand = false;
  // §16.12.17 Restriction 3: a recursive instance must occur after a positive
  // advance in time. Track whether any time-advancing operator has been seen
  // before a self-name instantiation.
  bool saw_time_advance = false;

  // §16.12.17 Restriction 4: capture the actual-argument shape of one property
  // instance. On entry the current token is the opening '(' of the argument
  // list; on return the matching ')' has been consumed. Nested instance
  // references found within the arguments are still recorded into
  // prop_instance_refs so the dependency digraph is unaffected.
  auto capture_instance_args = [&](std::string_view callee) {
    PropertyInstanceArgInfo info;
    info.callee = callee;
    Consume();  // '('
    int d = 1;
    std::vector<std::string_view> cur_idents;
    int cur_tokens = 0;
    bool arg_has_content = false;
    std::string_view prev_ident;
    bool prev_was_ident = false;
    auto finalize_arg = [&]() {
      info.arg_idents.push_back(cur_idents);
      info.arg_is_single_ident.push_back(cur_tokens == 1 &&
                                         cur_idents.size() == 1);
      cur_idents.clear();
      cur_tokens = 0;
    };
    while (d > 0 && !AtEnd()) {
      if (Check(TokenKind::kLParen)) {
        if (prev_was_ident) item->prop_instance_refs.push_back(prev_ident);
        Consume();
        ++d;
        ++cur_tokens;
        arg_has_content = true;
        prev_was_ident = false;
      } else if (Check(TokenKind::kRParen)) {
        Consume();
        --d;
        if (d == 0) {
          if (arg_has_content) finalize_arg();
          break;
        }
        ++cur_tokens;
        prev_was_ident = false;
      } else if (d == 1 && Check(TokenKind::kComma)) {
        Consume();
        finalize_arg();
        arg_has_content = true;
        prev_was_ident = false;
      } else if (Check(TokenKind::kIdentifier)) {
        auto t = Consume();
        cur_idents.push_back(t.text);
        ++cur_tokens;
        arg_has_content = true;
        prev_ident = t.text;
        prev_was_ident = true;
      } else {
        Consume();
        ++cur_tokens;
        arg_has_content = true;
        prev_was_ident = false;
      }
    }
    item->prop_instance_args.push_back(std::move(info));
  };

  while (!Check(TokenKind::kKwEndproperty) && !AtEnd()) {
    if (in_decl_prefix && IsBuiltinTypeKwForLocalVar(CurrentToken().kind)) {
      HarvestAssertionVariableDecl(item);
      continue;
    }
    in_decl_prefix = false;

    if (Check(TokenKind::kKwDisable)) {
      Consume();
      if (Check(TokenKind::kKwIff)) {
        Consume();
        ++item->prop_disable_iff_count;
      }
      continue;
    }
    if (Check(TokenKind::kKwCase)) {
      case_default_counts.push_back(0);
      Consume();
      continue;
    }
    if (Check(TokenKind::kKwEndcase)) {
      if (!case_default_counts.empty()) case_default_counts.pop_back();
      Consume();
      continue;
    }
    if (Check(TokenKind::kKwDefault) && !case_default_counts.empty()) {
      // §16.12.16: the default statement is optional, but using more than one
      // default in a single property case statement shall be illegal.
      auto default_loc = CurrentLoc();
      if (++case_default_counts.back() == 2) {
        diag_.Error(default_loc,
                    "property case statement shall have at most one 'default' "
                    "item");
      }
      Consume();
      continue;
    }
    // §16.12.17 Restriction 1: the prefix operators not, s_nexttime,
    // s_eventually, and s_always negate/strongly bind the property expression
    // that follows. s_until and s_until_with are infix; their right operand is
    // also a property expression. Mark that the next instance reached is one of
    // these operands. (s_nexttime also advances time for Restriction 3.)
    if (Check(TokenKind::kKwNot) || Check(TokenKind::kKwSNexttime) ||
        Check(TokenKind::kKwSEventually) || Check(TokenKind::kKwSAlways) ||
        Check(TokenKind::kKwSUntil) || Check(TokenKind::kKwSUntilWith)) {
      if (Check(TokenKind::kKwSNexttime)) saw_time_advance = true;
      expect_negated_operand = true;
      Consume();
      continue;
    }
    // §16.12.17 Restriction 3: ##, |=> (suffix non-overlapping implication),
    // and (s_)nexttime advance time. |-> (overlapping implication) does not.
    if (Check(TokenKind::kHashHash) || Check(TokenKind::kPipeEqGt) ||
        Check(TokenKind::kKwNexttime)) {
      saw_time_advance = true;
      Consume();
      continue;
    }
    if (Check(TokenKind::kIdentifier)) {
      auto tok = Consume();
      if (Check(TokenKind::kLParen)) {
        item->prop_instance_refs.push_back(tok.text);
        if (expect_negated_operand) {
          item->prop_negated_instance_refs.push_back(tok.text);
        }
        if (tok.text == item->name && !saw_time_advance) {
          item->prop_has_untimed_self_recursion = true;
        }
        expect_negated_operand = false;
        capture_instance_args(tok.text);
      } else {
        // A bare identifier is not a property instance; if it stood as the
        // operand of a pending negation, that operand is a simple expression.
        expect_negated_operand = false;
      }
      continue;
    }
    // Opening parentheses are skipped so a negation can still reach an instance
    // wrapped in parentheses; any other token ends a pending negation operand.
    if (!Check(TokenKind::kLParen)) expect_negated_operand = false;
    Consume();
  }
  Expect(TokenKind::kKwEndproperty);
  MatchEndLabel(item->name);
  return item;
}

namespace {

// §16.7: parse a plain decimal token like "5" into its integer value. Sized
// or based literals ("5'd10", "3'b101") return false; the caller leaves
// validation to downstream stages that have full constant-folding.
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
  // §16.7: only the literal `##[ [-]INTLIT : [-]INTLIT ]` form is checked
  // here. Symbolic bounds need full constant evaluation and are deferred to
  // later stages. The five-to-seven token window is peeked under SavePos so
  // the body loop still sees every token afterwards.
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

void Parser::HarvestAssertionVariableDecl(ModuleItem* item) {
  // §16.10 Syntax 16-13: assertion_variable_declaration ::= var_data_type
  // list_of_variable_decl_assignments ; — consume the data-type prefix
  // (one keyword plus any packed dimensions or signing token) and then walk
  // the comma-separated list of <identifier> [ = <expression> ] entries
  // until the closing semicolon. Each identifier names a distinct local
  // variable in the sequence/property body.
  Consume();  // var_data_type's leading type keyword.
  while (Check(TokenKind::kKwSigned) || Check(TokenKind::kKwUnsigned)) {
    Consume();
  }
  while (Check(TokenKind::kLBracket)) {
    int b_depth = 1;
    Consume();
    while (b_depth > 0 && !AtEnd()) {
      if (Check(TokenKind::kLBracket))
        ++b_depth;
      else if (Check(TokenKind::kRBracket))
        --b_depth;
      Consume();
    }
  }
  while (!Check(TokenKind::kSemicolon) && !AtEnd()) {
    if (Check(TokenKind::kIdentifier)) {
      auto tok = Consume();
      item->prop_seq_assert_vars.push_back(tok.text);
      if (Check(TokenKind::kEq)) {
        Consume();
        int e_depth = 0;
        while (!AtEnd()) {
          if (Check(TokenKind::kLParen) || Check(TokenKind::kLBracket) ||
              Check(TokenKind::kLBrace)) {
            ++e_depth;
            Consume();
          } else if (Check(TokenKind::kRParen) || Check(TokenKind::kRBracket) ||
                     Check(TokenKind::kRBrace)) {
            if (e_depth == 0) break;
            --e_depth;
            Consume();
          } else if (e_depth == 0 && (Check(TokenKind::kComma) ||
                                      Check(TokenKind::kSemicolon))) {
            break;
          } else {
            Consume();
          }
        }
      }
      if (Check(TokenKind::kComma)) Consume();
    } else {
      Consume();
    }
  }
  if (Check(TokenKind::kSemicolon)) Consume();
}

ModuleItem* Parser::ParseSequenceDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kSequenceDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwSequence);
  item->name = Expect(TokenKind::kIdentifier).text;

  // §16.8 sequence_port_list: harvest formal_port_identifier names so the
  // elaborator can flatten instances and run cycle detection.
  //
  // §16.8.2 local variable formal arguments: a port item may begin with the
  // keyword `local`, optionally followed by one of the directions `input`,
  // `inout`, or `output`. Two well-formedness rules are checked here:
  //   (a) a direction without a preceding `local` is illegal in a sequence
  //       port list;
  //   (b) a default actual argument is illegal for a local formal of
  //       direction `inout` or `output`.
  // For each local-marked formal we also record its (possibly inferred)
  // direction so later stages can apply the §16.10 local-variable rules.
  if (Match(TokenKind::kLParen)) {
    int depth = 1;
    bool expect_formal_name = true;

    bool item_saw_local = false;
    // §16.8.2 distinguishes "local was set by a keyword in this port item"
    // from "local was carried over via the inheritance rule." Only the
    // explicit-here case triggers the explicit-type-required check.
    bool item_local_explicit_here = false;
    // §16.8.2: a local formal must have its type specified explicitly in
    // the same port item. We mark `explicit type seen` when we consume a
    // built-in type keyword or when the formal-name harvest finds more than
    // one identifier in the chain (the first is a type alias).
    bool item_saw_explicit_type = false;
    Direction item_dir = Direction::kInput;
    bool item_saw_eq = false;
    SourceLoc item_start = CurrentLoc();

    auto finalize_port_item = [&]() {
      if (item_saw_local) {
        if (item_local_explicit_here && !item_saw_explicit_type) {
          diag_.Error(item_start,
                      "a local variable formal argument requires an explicit "
                      "type in its own port item (§16.8.2)");
        }
        if (item_saw_eq &&
            (item_dir == Direction::kInout || item_dir == Direction::kOutput)) {
          diag_.Error(item_start,
                      "default actual argument is illegal for a local "
                      "variable formal argument of direction inout or "
                      "output (§16.8.2)");
        }
        item->prop_seq_local_lvar_directions.push_back(item_dir);
      }
    };

    // §16.8.2 carry-through: a port item that supplies only an identifier
    // inherits the `local` designation, direction, and type of the nearest
    // preceding port item that declared them explicitly. A port item that
    // begins with `local`, a direction keyword, or a built-in type keyword
    // is a fresh starter and breaks the carry.
    auto reset_after_comma = [&]() {
      bool next_is_fresh_starter =
          Check(TokenKind::kKwLocal) || Check(TokenKind::kKwInput) ||
          Check(TokenKind::kKwOutput) || Check(TokenKind::kKwInout) ||
          IsBuiltinTypeKwForLocalVar(CurrentToken().kind);
      if (next_is_fresh_starter) {
        item_saw_local = false;
        item_dir = Direction::kInput;
      }
      // Else: carry item_saw_local and item_dir from the previous port item.
      // Per-port-item flags never carry: a carried port item neither sees
      // `local` explicitly here nor declares its own type.
      item_local_explicit_here = false;
      item_saw_explicit_type = false;
      item_saw_eq = false;
      expect_formal_name = true;
    };

    while (depth > 0 && !AtEnd()) {
      if (Check(TokenKind::kLParen)) {
        Consume();
        ++depth;
      } else if (Check(TokenKind::kRParen)) {
        if (depth == 1) finalize_port_item();
        Consume();
        --depth;
        if (depth == 0) break;
      } else if (depth == 1 && Check(TokenKind::kComma)) {
        finalize_port_item();
        Consume();
        item_start = CurrentLoc();
        reset_after_comma();
      } else if (depth == 1 && Check(TokenKind::kKwLocal)) {
        if (!item_saw_local) item_start = CurrentLoc();
        item_saw_local = true;
        item_local_explicit_here = true;
        Consume();
      } else if (depth == 1 &&
                 (Check(TokenKind::kKwInput) || Check(TokenKind::kKwOutput) ||
                  Check(TokenKind::kKwInout))) {
        auto dir_tok = Consume();
        if (!item_saw_local) {
          diag_.Error(dir_tok.loc,
                      "sequence port direction requires the 'local' keyword "
                      "(§16.8.2)");
        }
        if (dir_tok.kind == TokenKind::kKwInput) {
          item_dir = Direction::kInput;
        } else if (dir_tok.kind == TokenKind::kKwOutput) {
          item_dir = Direction::kOutput;
        } else {
          item_dir = Direction::kInout;
        }
      } else if (depth == 1 &&
                 IsBuiltinTypeKwForLocalVar(CurrentToken().kind)) {
        Consume();
        item_saw_explicit_type = true;
      } else if (depth == 1 && Check(TokenKind::kEq)) {
        item_saw_eq = true;
        Consume();
        expect_formal_name = false;
      } else if (depth == 1 && expect_formal_name &&
                 Check(TokenKind::kIdentifier)) {
        auto name_tok = Consume();
        // Walk past any subsequent identifiers/type tokens until we hit the
        // separator; the rightmost identifier is the formal_port_identifier.
        // §16.8.2: a chain of more than one identifier means the leading
        // identifier(s) supply a (user-defined) type alias, satisfying the
        // explicit-type requirement.
        while (Check(TokenKind::kIdentifier)) {
          name_tok = Consume();
          item_saw_explicit_type = true;
        }
        item->prop_formals.push_back(name_tok.text);
        expect_formal_name = false;
      } else {
        Consume();
      }
    }
  }

  Expect(TokenKind::kSemicolon);

  // §16.10: assertion_variable_declarations precede the sequence_expr in the
  // body. We harvest them while still at the head of the body; once we see a
  // token that does not start a declaration we fall through to the existing
  // sequence_instance reference scan used for the §16.8 cycle rule.
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
