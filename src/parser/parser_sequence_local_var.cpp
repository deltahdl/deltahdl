#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "parser/parser.h"
#include "parser/parser_property_grammar.h"
#include "parser/parser_property_spec_internal.h"
#include "parser/parser_sequence_property_decl_internal.h"

namespace delta {

namespace {

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

bool IsEventFormalOf(const ModuleItem* item, std::string_view name) {
  for (size_t i = 0; i < item->prop_formals.size(); ++i) {
    if (item->prop_formals[i] == name) {
      return item->prop_formal_type_kw[i] == TokenKind::kKwEvent;
    }
  }
  return false;
}

bool IsWholeInstanceActual(const ModuleItem* item, SourceLoc loc) {
  for (const auto& arg : item->assertion_instance_args) {
    if (arg.loc.file_id == loc.file_id && arg.loc.line == loc.line &&
        arg.loc.column == loc.column) {
      return true;
    }
  }
  return false;
}

void ReportEventFormalReference(DiagEngine& diag, const ModuleItem* item,
                                const Token& tok, bool after_select) {
  if (after_select || !IsEventFormalOf(item, tok.text) ||
      IsWholeInstanceActual(item, tok.loc)) {
    return;
  }
  diag.Error(tok.loc,
             "formal argument '" + std::string(tok.text) +
                 "' of type event is referenced where no event expression may "
                 "be written",
             Subclause("16.8.1"));
}

}  // namespace

void ReportChandleFormal(DiagEngine& diag, const Token& type_tok) {
  if (type_tok.kind != TokenKind::kKwChandle) return;
  diag.Error(type_tok.loc,
             "a sequence or property formal argument may not be of type "
             "chandle",
             Subclause("16.8"));
}

bool IsDisallowedLocalVarTypeKw(TokenKind k) {
  switch (k) {
    case TokenKind::kKwEvent:
    case TokenKind::kKwSequence:
    case TokenKind::kKwProperty:
    case TokenKind::kKwUntyped:
      return true;
    default:
      return false;
  }
}

void Parser::ValidateLiteralCycleDelayRange(SourceLoc range_loc) {
  if (!Check(TokenKind::kLBracket)) return;
  auto saved = lexer_.SavePos();
  Consume();
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
  Consume();
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

  if (lo_negative || hi_negative) {
    diag_.Error(range_loc, "cycle-delay range bounds cannot be negative",
                Subclause("16.7"));
    return;
  }
  if (hi_mag < lo_mag) {
    diag_.Error(range_loc,
                "cycle-delay range upper bound must be at least the lower "
                "bound",
                Subclause("16.7"));
  }
}

static void ScanMinTypMaxToken(TokenKind k, int& nesting, int& cond_depth,
                               bool& is_min_typ_max) {
  if (k == TokenKind::kLParen || k == TokenKind::kLBracket ||
      k == TokenKind::kLBrace) {
    ++nesting;
    return;
  }
  if (k == TokenKind::kRParen || k == TokenKind::kRBracket ||
      k == TokenKind::kRBrace) {
    --nesting;
    return;
  }
  if (nesting != 1) return;
  if (k == TokenKind::kQuestion) {
    ++cond_depth;
    return;
  }
  if (k != TokenKind::kColon) return;
  if (cond_depth > 0) {
    --cond_depth;
  } else {
    is_min_typ_max = true;
  }
}

void Parser::ValidateCycleDelayMinTypMax(SourceLoc range_loc) {
  if (!Check(TokenKind::kLParen)) return;
  auto saved = lexer_.SavePos();
  Consume();
  int nesting = 1;
  int cond_depth = 0;
  bool is_min_typ_max = false;
  while (nesting > 0 && !Check(TokenKind::kEof)) {
    ScanMinTypMaxToken(CurrentToken().kind, nesting, cond_depth,
                       is_min_typ_max);
    Consume();
  }
  lexer_.RestorePos(saved);
  if (is_min_typ_max) {
    diag_.Error(range_loc,
                "a min:typ:max expression may not be used as a cycle-delay "
                "value",
                Subclause("16.7"));
  }
}

void Parser::ValidateCycleDelayIntegerValue(SourceLoc range_loc) {
  if (Check(TokenKind::kRealLiteral) || Check(TokenKind::kStringLiteral)) {
    diag_.Error(range_loc, "cycle-delay value must be an integer",
                Subclause("16.7"));
  }
}

static void SkipGroups(Lexer& lexer, TokenKind open, TokenKind close) {
  while (LexerCheck(lexer, open)) {
    int depth = 1;
    lexer.Next();
    while (depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
      if (LexerCheck(lexer, open))
        ++depth;
      else if (LexerCheck(lexer, close))
        --depth;
      lexer.Next();
    }
  }
}

static void SkipBracketGroups(Lexer& lexer) {
  SkipGroups(lexer, TokenKind::kLBracket, TokenKind::kRBracket);
}

static bool SkipTypeName(Lexer& lexer) {
  bool scoped = false;
  while (LexerCheck(lexer, TokenKind::kIdentifier)) {
    lexer.Next();
    if (LexerCheck(lexer, TokenKind::kHash)) {
      lexer.Next();
      SkipGroups(lexer, TokenKind::kLParen, TokenKind::kRParen);
    }
    if (!LexerCheck(lexer, TokenKind::kColonColon)) break;
    lexer.Next();
    scoped = true;
  }
  return scoped;
}

static bool AtTypeNameBeforeIdentifier(Lexer& lexer) {
  auto saved = lexer.SavePos();
  SkipTypeName(lexer);
  SkipBracketGroups(lexer);
  const bool kTyped = LexerCheck(lexer, TokenKind::kIdentifier);
  lexer.RestorePos(saved);
  return kTyped;
}

bool VarWritesDataType(Lexer& lexer) {
  if (IsBuiltinTypeKwForLocalVar(lexer.Peek().kind)) return true;
  return LexerCheck(lexer, TokenKind::kIdentifier) &&
         AtTypeNameBeforeIdentifier(lexer);
}

bool AtAssertionVariableDecl(
    Lexer& lexer, const std::unordered_set<std::string_view>& known_types) {
  const Token kType = lexer.Peek();
  if (kType.kind == TokenKind::kKwVar ||
      IsBuiltinTypeKwForLocalVar(kType.kind)) {
    return true;
  }
  if (kType.kind != TokenKind::kIdentifier) return false;
  auto saved = lexer.SavePos();
  const bool kScoped = SkipTypeName(lexer);
  lexer.RestorePos(saved);
  if (kScoped) return AtTypeNameBeforeIdentifier(lexer);
  if (!known_types.contains(kType.text)) return false;
  lexer.Next();
  const bool kDeclares = LexerCheck(lexer, TokenKind::kIdentifier) ||
                         LexerCheck(lexer, TokenKind::kLBracket);
  lexer.RestorePos(saved);
  return kDeclares;
}

static void SkipAssertVarTypePrefix(Lexer& lexer) {
  const bool kVar = LexerCheck(lexer, TokenKind::kKwVar);
  if (kVar) lexer.Next();
  if (!kVar || VarWritesDataType(lexer)) {
    if (LexerCheck(lexer, TokenKind::kIdentifier)) {
      SkipTypeName(lexer);
    } else {
      lexer.Next();
    }
  }
  while (LexerCheck(lexer, TokenKind::kKwSigned) ||
         LexerCheck(lexer, TokenKind::kKwUnsigned)) {
    lexer.Next();
  }
  SkipBracketGroups(lexer);
}

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
  auto type_pos = lexer_.SavePos();
  Match(TokenKind::kKwVar);
  if (Check(TokenKind::kKwChandle)) {
    diag_.Error(CurrentLoc(),
                "an assertion variable may not be declared of type chandle",
                Subclause("16.10"));
  }
  lexer_.RestorePos(type_pos);
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

struct SequencePortScan {
  Parser* parser = nullptr;
  int depth = 1;
  bool expect_formal_name = true;

  bool item_saw_local = false;
  bool item_local_explicit_here = false;
  bool item_saw_explicit_type = false;
  Direction item_dir = Direction::kInput;
  bool item_saw_eq = false;
  SourceLoc item_start;
  TokenKind prev_kind = TokenKind::kComma;
  TokenKind carry_type_kw = TokenKind::kEof;
  DataType* carry_type = nullptr;
  bool clock_default_allowed = true;
  PortItemShape shape{"sequence"};

  void FinalizePortItem(DiagEngine& diag, ModuleItem* item) {
    if (!item_saw_local) return;
    if (item_local_explicit_here && !item_saw_explicit_type) {
      diag.Error(item_start,
                 "a local variable formal argument requires an explicit "
                 "type in its own port item",
                 Subclause("16.8.2"));
    }
    if (item_saw_eq &&
        (item_dir == Direction::kInout || item_dir == Direction::kOutput)) {
      diag.Error(item_start,
                 "default actual argument is illegal for a local "
                 "variable formal argument of direction inout or "
                 "output",
                 Subclause("16.8.2"));
    }
    item->prop_seq_local_lvar_directions.push_back(item_dir);
  }

  void ResetAfterComma(Lexer& lexer) {
    bool next_is_fresh_starter = LexerCheck(lexer, TokenKind::kKwLocal) ||
                                 LexerCheck(lexer, TokenKind::kKwInput) ||
                                 LexerCheck(lexer, TokenKind::kKwOutput) ||
                                 LexerCheck(lexer, TokenKind::kKwInout) ||
                                 IsBuiltinTypeKwForLocalVar(lexer.Peek().kind);
    if (next_is_fresh_starter) {
      item_saw_local = false;
      item_dir = Direction::kInput;
    }
    item_local_explicit_here = false;
    item_saw_explicit_type = false;
    item_saw_eq = false;
    expect_formal_name = true;
  }

  void HandleDirection(Lexer& lexer, DiagEngine& diag) {
    auto dir_tok = lexer.Next();
    if (!item_saw_local) {
      diag.Error(dir_tok.loc,
                 "sequence port direction requires the 'local' keyword",
                 Subclause("16.8.2"));
    }
    if (dir_tok.kind == TokenKind::kKwInput) {
      item_dir = Direction::kInput;
    } else if (dir_tok.kind == TokenKind::kKwOutput) {
      item_dir = Direction::kOutput;
    } else {
      item_dir = Direction::kInout;
    }
  }

  void HarvestFormalName(Lexer& lexer, ModuleItem* item) {
    if (!shape.typed &&
        ParserPropertySpecHelpers::StartsNamedFormalType(*parser)) {
      carry_type = ParserPropertySpecHelpers::ParseNamedFormalType(*parser);
      carry_type_kw = TokenKind::kEof;
      item_saw_explicit_type = true;
      clock_default_allowed = false;
    }
    auto name_tok = lexer.Next();
    item->prop_formals.push_back(name_tok.text);
    bool untyped = carry_type_kw == TokenKind::kEof && clock_default_allowed;
    item->prop_formal_type_kw.push_back(untyped ? TokenKind::kKwUntyped
                                                : carry_type_kw);
    item->prop_formal_types.push_back(carry_type);
    item->prop_formal_unpacked_dims.emplace_back();
    item->prop_formal_is_local.push_back(item_saw_local);
    item->prop_formal_has_default.push_back(false);
    item->prop_formal_defaults.push_back(nullptr);
    item->prop_formal_inferred.push_back(InferredDefault::kNone);
    expect_formal_name = false;
    shape.NameFormal();
  }

  void HandleComma(Lexer& lexer, DiagEngine& diag, ModuleItem* item) {
    FinalizePortItem(diag, item);
    shape.End(diag);
    lexer.Next();
    shape.Begin(lexer.Peek());
    item_start = lexer.Peek().loc;
    ResetAfterComma(lexer);
  }

  void HandleLocal(Lexer& lexer) {
    if (!item_saw_local) item_start = lexer.Peek().loc;
    item_saw_local = true;
    item_local_explicit_here = true;
    lexer.Next();
  }

  bool HandleTypeKeyword(Lexer& lexer, DiagEngine& diag) {
    TokenKind kind = lexer.Peek().kind;
    if (IsBuiltinTypeKwForLocalVar(kind)) {
      ReportChandleFormal(diag, lexer.Peek());
      carry_type = ParserPropertySpecHelpers::ParseFormalType(*parser);
      carry_type_kw =
          carry_type->packed_dim_left != nullptr ? TokenKind::kEof : kind;
      item_saw_explicit_type = true;
      clock_default_allowed = false;
      shape.typed = true;
      return true;
    }
    if (item_saw_local || !IsDisallowedLocalVarTypeKw(kind)) return false;
    lexer.Next();
    shape.typed = true;
    carry_type_kw = kind == TokenKind::kKwUntyped ? TokenKind::kEof : kind;
    carry_type = nullptr;
    clock_default_allowed =
        kind == TokenKind::kKwUntyped || kind == TokenKind::kKwEvent;
    return true;
  }

  void HandleDefaultEq(Lexer& lexer, ModuleItem* item) {
    item_saw_eq = true;
    shape.BeginDefault();
    if (!item->prop_formal_has_default.empty()) {
      item->prop_formal_has_default.back() = true;
    }
    lexer.Next();
    expect_formal_name = false;
    RecordDefault(item);
  }

  void RecordDefault(ModuleItem* item) {
    if (parser == nullptr || item->prop_formal_defaults.empty()) return;
    item->prop_formal_defaults.back() =
        ParserPropertySpecHelpers::ParseFormalDefault(*parser);
  }

  bool DispatchTopLevel(Lexer& lexer, DiagEngine& diag, ModuleItem* item) {
    if (LexerCheck(lexer, TokenKind::kComma)) {
      HandleComma(lexer, diag, item);
    } else if (LexerCheck(lexer, TokenKind::kKwLocal)) {
      HandleLocal(lexer);
    } else if (LexerCheck(lexer, TokenKind::kKwInput) ||
               LexerCheck(lexer, TokenKind::kKwOutput) ||
               LexerCheck(lexer, TokenKind::kKwInout)) {
      HandleDirection(lexer, diag);
    } else if (HandleTypeKeyword(lexer, diag)) {
    } else if (item_saw_local &&
               IsDisallowedLocalVarTypeKw(lexer.Peek().kind)) {
      diag.Error(lexer.Peek().loc,
                 "the type of a local variable formal argument must be one of "
                 "the types allowed in §16.6",
                 Subclause("16.8.2"));
      item_saw_explicit_type = true;
      shape.typed = true;
      lexer.Next();
    } else if (LexerCheck(lexer, TokenKind::kEq)) {
      HandleDefaultEq(lexer, item);
    } else if (prev_kind == TokenKind::kEq &&
               LexerCheck(lexer, TokenKind::kSystemIdentifier)) {
      ScanSystemDefaultValue(lexer, diag, item, clock_default_allowed);
    } else if (expect_formal_name &&
               LexerCheck(lexer, TokenKind::kIdentifier)) {
      HarvestFormalName(lexer, item);
    } else {
      return false;
    }
    return true;
  }

  bool Step(Lexer& lexer, DiagEngine& diag, ModuleItem* item) {
    TokenKind this_kind = lexer.Peek().kind;
    if (depth == 1 && this_kind != TokenKind::kRParen) {
      shape.Begin(lexer.Peek());
    }
    bool keep_going = StepDispatch(lexer, diag, item);
    prev_kind = this_kind;
    return keep_going;
  }

  bool StepDispatch(Lexer& lexer, DiagEngine& diag, ModuleItem* item) {
    if (depth == 1 &&
        (shape.SkipAttributes(lexer) || shape.SkipTailToken(lexer, diag))) {
      return true;
    }
    if (LexerCheck(lexer, TokenKind::kLParen)) {
      lexer.Next();
      ++depth;
      return true;
    }
    if (LexerCheck(lexer, TokenKind::kRParen)) {
      if (depth == 1) {
        FinalizePortItem(diag, item);
        shape.End(diag);
      }
      lexer.Next();
      --depth;
      return depth != 0;
    }
    if (depth == 1 && DispatchTopLevel(lexer, diag, item)) return true;
    lexer.Next();
    return true;
  }
};

static void ParseSequencePortList(Parser& parser, Lexer& lexer,
                                  DiagEngine& diag, ModuleItem* item) {
  SequencePortScan scan;
  scan.parser = &parser;
  scan.item_start = lexer.Peek().loc;
  while (scan.depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (!scan.Step(lexer, diag, item)) break;
  }
}

ModuleItem* Parser::ParseSequenceDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kSequenceDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwSequence, Subclause("16.8"));
  item->name = Expect(TokenKind::kIdentifier, Subclause("16.8")).text;

  if (Match(TokenKind::kLParen)) {
    ParseSequencePortList(*this, lexer_, diag_, item);
  }

  Expect(TokenKind::kSemicolon, Subclause("16.8"));
  ParserPropertySpecHelpers::RecordAssertionReads(*this, item,
                                                  TokenKind::kKwEndsequence);

  item->decl_has_leading_clock = Check(TokenKind::kAt);

  CaptureLinearSequenceBody(item);

  ScanSequenceBody(item);
  Expect(TokenKind::kKwEndsequence, Subclause("16.8"));
  MatchEndLabel(item->name);
  return item;
}

void Parser::ScanSequenceClockEvent(ModuleItem* item) {
  ++item->decl_clock_event_count;
  Consume();
  if (Check(TokenKind::kIdentifier)) {
    item->prop_instance_refs.push_back(Consume().text);
    return;
  }
  ScanClockEventGroupForLocals(lexer_, diag_, item);
}

void Parser::ScanSequenceBody(ModuleItem* item) {
  while (AtAssertionVariableDecl(lexer_, known_types_)) {
    HarvestAssertionVariableDecl(item);
  }
  ParserPropertyGrammar::CheckDeclarationBody(*this, true,
                                              TokenKind::kKwEndsequence);
  bool after_select = false;
  while (!Check(TokenKind::kKwEndsequence) && !AtEnd()) {
    if (Check(TokenKind::kAt)) {
      ScanSequenceClockEvent(item);
      continue;
    }
    if (Check(TokenKind::kHashHash)) {
      auto delay_loc = CurrentLoc();
      Consume();
      ValidateLiteralCycleDelayRange(delay_loc);
      ValidateCycleDelayMinTypMax(delay_loc);
      ValidateCycleDelayIntegerValue(delay_loc);
      continue;
    }
    if (Check(TokenKind::kIdentifier)) {
      auto tok = Consume();
      ReportEventFormalReference(diag_, item, tok, after_select);
      after_select = false;
      item->prop_instance_refs.push_back(tok.text);
      continue;
    }
    after_select = Check(TokenKind::kDot) || Check(TokenKind::kColonColon);
    Consume();
  }
}

DataType* ParserPropertySpecHelpers::ParseFormalType(Parser& p) {
  return p.arena_.Create<DataType>(p.ParseDataType());
}

bool ParserPropertySpecHelpers::StartsNamedFormalType(Parser& p) {
  auto saved = p.lexer_.SavePos();
  p.Consume();
  int depth = 0;
  while (!p.Check(TokenKind::kEof)) {
    TokenKind k = p.CurrentToken().kind;
    if (k == TokenKind::kLParen || k == TokenKind::kLBracket) {
      ++depth;
    } else if (k == TokenKind::kRParen || k == TokenKind::kRBracket) {
      if (depth == 0) break;
      --depth;
    } else if (depth == 0 && k == TokenKind::kColonColon) {
      p.Consume();
    } else if (depth == 0 && k != TokenKind::kHash) {
      break;
    }
    p.Consume();
  }
  bool typed = depth == 0 && p.Check(TokenKind::kIdentifier);
  p.lexer_.RestorePos(saved);
  return typed;
}

DataType* ParserPropertySpecHelpers::ParseNamedFormalType(Parser& p) {
  auto* type = p.arena_.Create<DataType>(p.ParseNamedType());
  p.ParsePackedDims(*type);
  return type;
}

}  // namespace delta
