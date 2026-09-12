#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "parser/parser.h"

namespace delta {

ModuleDecl* Parser::ParseCheckerDecl() {
  auto* decl = arena_.Create<ModuleDecl>();
  TypeNameScope type_scope(*this);
  decl->decl_kind = ModuleDeclKind::kChecker;
  decl->range.start = CurrentLoc();
  Expect(TokenKind::kKwChecker, Subclause("17.2"));
  decl->name = Expect(TokenKind::kIdentifier, Subclause("17.2")).text;
  ParseParamsPortsAndSemicolon(*decl);

  auto* prev_module = current_module_;
  current_module_ = decl;
  while (!Check(TokenKind::kKwEndchecker) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    ParseModuleItem(decl->items);
  }
  current_module_ = prev_module;
  Expect(TokenKind::kKwEndchecker, Subclause("17.2"));
  MatchEndLabel(decl->name);
  decl->range.end = CurrentLoc();
  return decl;
}

static bool IsBinsKeyword(TokenKind k) {
  return k == TokenKind::kKwBins || k == TokenKind::kKwIllegalBins ||
         k == TokenKind::kKwIgnoreBins;
}

static bool IsOptionKeyword(std::string_view text) {
  return text == "option" || text == "type_option";
}

// A.2.11 writes a coverage_option as `option . member_identifier = expression`
// or `type_option . member_identifier = constant_expression`, and §19.7 has
// an option take effect by that assignment alone: a member named with no
// value, or a keyword with no member, sets nothing. Positioned on the `option`
// or `type_option` keyword; reads it, the '.' and the member, and stops on the
// '=', which the caller's scan of the value takes. Returns the member once it
// is read, whether or not the '=' follows, so a caller keying on the member
// still keys on it; a break in the form is reported where the form breaks.
static std::optional<Token> ReadCoverageOptionMember(Lexer& lexer,
                                                     DiagEngine& diag) {
  Token keyword = lexer.Next();
  auto report = [&](SourceLoc loc) {
    diag.Error(loc,
               "a coverage option is set as '" + std::string(keyword.text) +
                   ".member = value'",
               Subclause("A.2.11"));
  };
  if (!lexer.Peek().Is(TokenKind::kDot)) {
    report(lexer.Peek().loc);
    return std::nullopt;
  }
  lexer.Next();
  if (!lexer.Peek().Is(TokenKind::kIdentifier)) {
    report(lexer.Peek().loc);
    return std::nullopt;
  }
  Token member = lexer.Next();
  if (!lexer.Peek().Is(TokenKind::kEq)) report(lexer.Peek().loc);
  return member;
}

enum class CovBodyStep : uint8_t { kNotHandled, kContinue, kReturn };

// The two lower syntactic levels a coverage option can be attached to inside a
// covergroup body (LRM 19.7, Table 19-2). The covergroup level itself accepts
// every instance option and so is not represented here.
enum class CovItemLevel : uint8_t { kCoverpoint, kCross };

// How a bins name is subscripted: not at all, `[ ]`, or `[ expression ]`.
// A.2.11's bins_or_options puts `[ [ covergroup_expression ] ]` after the
// name of a bin over values and `[ ]` alone after the name of a bin over
// transitions, and its bins_selection, the form a cross_body holds, admits
// neither.
enum class BinsSubscript : uint8_t { kNone, kEmpty, kSized };

// Reads the subscript after a bins name, `[` already seen, up to its `]`.
static BinsSubscript ScanBinsSubscript(Lexer& lexer, DiagEngine& diag,
                                       CovItemLevel level) {
  if (level == CovItemLevel::kCross) {
    diag.Error(lexer.Peek().loc,
               "a cross bin is not an array; a bins_selection subscripts "
               "nothing",
               Subclause("A.2.11"));
  }
  lexer.Next();  // [
  BinsSubscript subscript = BinsSubscript::kEmpty;
  int bd = 1;
  while (bd > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (lexer.Peek().Is(TokenKind::kLBracket)) {
      ++bd;
    } else if (lexer.Peek().Is(TokenKind::kRBracket)) {
      --bd;
    } else {
      subscript = BinsSubscript::kSized;
    }
    lexer.Next();
  }
  return subscript;
}

// Holds what a bins value opens with to the subscript and the `wildcard`
// before it. `wildcard` is written on A.2.11's four value and transition
// forms and on neither `default` form; `default sequence` carries no
// subscript; a trans_list follows `[ ]` alone, §19.5.2 (printed page 592)
// naming its bins "binname[transition]" for the transitions the list holds
// rather than for a size the declaration gives. A cross_body's bins_selection
// takes a select_expression, of which `default` is no form.
static void CheckBinsValueHead(Lexer& lexer, DiagEngine& diag,
                               CovItemLevel level,
                               const std::optional<Token>& wildcard,
                               BinsSubscript subscript) {
  Token head = lexer.Peek();
  if (head.Is(TokenKind::kKwDefault)) {
    if (level == CovItemLevel::kCross) {
      diag.Error(head.loc,
                 "a cross bin selects with a select_expression; 'default' "
                 "is a coverpoint bin",
                 Subclause("A.2.11"));
    }
    if (wildcard) {
      diag.Error(wildcard->loc,
                 "'wildcard' qualifies a bin over values or transitions; a "
                 "'default' bin takes none",
                 Subclause("A.2.11"));
    }
    lexer.Next();
    if (lexer.Peek().Is(TokenKind::kKwSequence) &&
        subscript != BinsSubscript::kNone) {
      diag.Error(lexer.Peek().loc, "a 'default sequence' bin is not an array",
                 Subclause("A.2.11"));
    }
    return;
  }
  if (head.Is(TokenKind::kLParen) && subscript == BinsSubscript::kSized) {
    diag.Error(head.loc,
               "a transition bin's array is written '[ ]'; its size is the "
               "number of transitions",
               Subclause("A.2.11"));
  }
}

// §19.5: a bins selection is `bins_keyword name [array] = ...`. Consume the
// keyword, name, and optional array dimension already known to lead the item,
// then require the '=' that every bins form has, and hold what follows it to
// the forms the subscript and a preceding `wildcard` leave open.
static void ScanBinsSelectionHeader(Lexer& lexer, DiagEngine& diag,
                                    CovItemLevel level,
                                    const std::optional<Token>& wildcard) {
  lexer.Next();  // bins keyword
  if (lexer.Peek().Is(TokenKind::kIdentifier)) lexer.Next();
  BinsSubscript subscript = BinsSubscript::kNone;
  if (lexer.Peek().Is(TokenKind::kLBracket)) {
    subscript = ScanBinsSubscript(lexer, diag, level);
  }
  if (!lexer.Peek().Is(TokenKind::kEq)) {
    diag.Error(lexer.Peek().loc, "expected '=' in bins declaration",
               Subclause("19.5.1"));
    return;
  }
  lexer.Next();  // =
  CheckBinsValueHead(lexer, diag, level, wildcard, subscript);
}

// §19.7, Table 19-2: report whether an instance coverage option named by
// `member` may NOT be specified at the given coverpoint/cross level. Only the
// options the table forbids at a lower level are listed; every other member
// (including options legal here and any name outside the table) is left alone.
// type_option members are governed by §19.7.1 and are not considered here.
static bool InstanceOptionForbiddenAtItemLevel(std::string_view member,
                                               CovItemLevel level) {
  // Covergroup-level-only options are forbidden at both lower levels.
  if (member == "name" || member == "per_instance" ||
      member == "get_inst_coverage") {
    return true;
  }
  if (level == CovItemLevel::kCoverpoint) {
    // The cross-only options are forbidden at the coverpoint level.
    return member == "cross_num_print_missing" ||
           member == "cross_retain_auto_bins";
  }
  // The coverpoint-only options are forbidden at the cross level.
  return member == "auto_bin_max" || member == "detect_overlap";
}

// §19.7, Table 19-2: an instance coverage option set inside a coverpoint or
// cross body is written `option . member = expression`. A member that may not
// be specified at this syntactic level is rejected. A `type_option` is read
// for its form alone, §19.7.1 governing which of its members stand where.
static void ScanItemLevelCoverageOption(Lexer& lexer, DiagEngine& diag,
                                        CovItemLevel level) {
  bool instance = lexer.Peek().text == "option";
  std::optional<Token> member = ReadCoverageOptionMember(lexer, diag);
  if (!member || !instance) return;
  if (InstanceOptionForbiddenAtItemLevel(member->text, level)) {
    diag.Error(member->loc,
               "coverage option 'option." + std::string(member->text) +
                   "' may not be specified at the " +
                   std::string(level == CovItemLevel::kCross ? "cross"
                                                             : "coverpoint") +
                   " level",
               Subclause("19.7"));
  }
}

// Reads the `wildcard` a bins item opens with. A.2.11 writes it on
// bins_or_options alone, the form a cover_point's body holds; the
// bins_selection of a cross_body admits none, so at cross level it is
// reported where it stands.
static Token ScanWildcardPrefix(Lexer& lexer, DiagEngine& diag,
                                CovItemLevel level) {
  Token wildcard = lexer.Next();
  if (level == CovItemLevel::kCross) {
    diag.Error(wildcard.loc,
               "a cross bin is not a wildcard bin; a bins_selection admits "
               "no 'wildcard'",
               Subclause("A.2.11"));
  }
  return wildcard;
}

// Handle a token seen at item level (body brace depth 1, no open parens),
// reporting the missing ';' / '=' diagnostics. Returns kNotHandled when the
// token is ordinary value content for the caller's nesting scan to consume.
static CovBodyStep ScanCoverpointItemToken(Lexer& lexer, DiagEngine& diag,
                                           CovItemLevel level,
                                           bool& item_active) {
  Token t = lexer.Peek();
  if (t.Is(TokenKind::kRBrace)) {
    if (item_active)
      diag.Error(t.loc, "missing ';' in covergroup item", Subclause("19.3"));
    lexer.Next();
    return CovBodyStep::kReturn;
  }
  if (t.Is(TokenKind::kSemicolon)) {
    item_active = false;
    lexer.Next();
    return CovBodyStep::kContinue;
  }
  // 'wildcard' is a prefix of the following bins selection; consume it without
  // starting a fresh item so the bins keyword sees the prior termination state.
  std::optional<Token> wildcard;
  if (t.Is(TokenKind::kKwWildcard)) {
    wildcard = ScanWildcardPrefix(lexer, diag, level);
    t = lexer.Peek();
    if (!IsBinsKeyword(t.kind)) return CovBodyStep::kContinue;
  }
  if (IsBinsKeyword(t.kind)) {
    if (item_active)
      diag.Error(t.loc, "missing ';' in covergroup item", Subclause("19.3"));
    item_active = true;
    ScanBinsSelectionHeader(lexer, diag, level, wildcard);
    return CovBodyStep::kContinue;
  }
  if (t.Is(TokenKind::kIdentifier) && IsOptionKeyword(t.text)) {
    ScanItemLevelCoverageOption(lexer, diag, level);
    return CovBodyStep::kContinue;
  }
  return CovBodyStep::kNotHandled;
}

// Consume one ordinary token, tracking brace/paren nesting. Returns kReturn
// once the body's closing brace is consumed (reporting an unbalanced paren).
static CovBodyStep ScanCoverpointNesting(Lexer& lexer, DiagEngine& diag,
                                         int& brace, int& paren) {
  Token t = lexer.Peek();
  if (t.Is(TokenKind::kLBrace)) {
    ++brace;
  } else if (t.Is(TokenKind::kRBrace)) {
    --brace;
    if (brace == 0) {
      if (paren > 0)
        diag.Error(t.loc, "missing ')' in covergroup item", Subclause("19.3"));
      lexer.Next();
      return CovBodyStep::kReturn;
    }
  } else if (t.Is(TokenKind::kLParen)) {
    ++paren;
  } else if (t.Is(TokenKind::kRParen)) {
    if (paren > 0) --paren;
  }
  lexer.Next();
  return CovBodyStep::kContinue;
}

// §19.5/§19.6: validate the brace-delimited body of a coverpoint or cross. The
// opening '{' has already been consumed (body brace depth starts at 1). Beyond
// balancing braces, this enforces the bin-syntax points exercised by the
// malformed-bins tests: a bins selection needs '=' after its (optionally
// indexed) name, each item ends with ';', and parentheses (e.g. binsof(...))
// must balance before the item terminates. Everything else is tolerated so the
// many legal bin forms continue to parse.
static void ScanCoverpointBraceBody(Lexer& lexer, DiagEngine& diag,
                                    CovItemLevel level) {
  int brace = 1;  // the coverpoint/cross body itself
  int paren = 0;
  bool item_active = false;
  while (!lexer.Peek().Is(TokenKind::kEof)) {
    if (brace == 1 && paren == 0) {
      CovBodyStep step =
          ScanCoverpointItemToken(lexer, diag, level, item_active);
      if (step == CovBodyStep::kReturn) return;
      if (step == CovBodyStep::kContinue) continue;
    }
    if (ScanCoverpointNesting(lexer, diag, brace, paren) ==
        CovBodyStep::kReturn) {
      return;
    }
  }
}

static void SkipCoverpointBody(Lexer& lexer, DiagEngine& diag,
                               CovItemLevel level) {
  while (!lexer.Peek().Is(TokenKind::kSemicolon) &&
         !lexer.Peek().Is(TokenKind::kLBrace) &&
         !lexer.Peek().Is(TokenKind::kEof)) {
    lexer.Next();
  }
  if (lexer.Peek().Is(TokenKind::kLBrace)) {
    lexer.Next();
    ScanCoverpointBraceBody(lexer, diag, level);
  }
  if (lexer.Peek().Is(TokenKind::kSemicolon)) lexer.Next();
}

void Parser::ParseBlockEventExpression() {
  do {
    if (!Check(TokenKind::kKwBegin) && !Check(TokenKind::kKwEnd)) {
      diag_.Error(CurrentLoc(), "expected 'begin' or 'end' in block event",
                  Subclause("19.3"));
      return;
    }
    Consume();
    ParseHierarchicalBtfIdentifier();
  } while (Match(TokenKind::kKwOr));
}

// Reads A.2.11's hierarchical_btf_identifier, a hierarchical_tf_identifier, a
// hierarchical_block_identifier or `[ hierarchical_identifier . | class_scope
// ] method_identifier`, where A.9.3 spells hierarchical_identifier `[ $root .
// ] { identifier constant_bit_select . } identifier` and A.8.4 spells
// class_scope `class_type ::` with class_type `ps_class_identifier [
// parameter_value_assignment ] { :: class_identifier [
// parameter_value_assignment ] }`. §19.3 (printed page 577) says what the
// name denotes, "a named block, task, function, or class method". The three
// forms share their first identifier and differ in what separates the
// identifiers after it, so the separators are read as they come. Nothing
// records the name: no reader of the tree consumes a coverage event.
void Parser::ParseHierarchicalBtfIdentifier() {
  if (Check(TokenKind::kSystemIdentifier) && CurrentToken().text == "$root") {
    Consume();
    Expect(TokenKind::kDot, Subclause("A.2.11"));
  }
  ExpectIdentifier(Subclause("A.2.11"));
  while (true) {
    if (Match(TokenKind::kLBracket)) {
      ParseExpr();
      Expect(TokenKind::kRBracket, Subclause("A.2.11"));
    } else if (Match(TokenKind::kDot) || Match(TokenKind::kColonColon)) {
      ExpectIdentifier(Subclause("A.2.11"));
    } else if (Match(TokenKind::kHash)) {
      std::vector<std::pair<std::string_view, Expr*>> params;
      ParseParamValueAssignment(params);
    } else {
      return;
    }
  }
}

// Classify the current token and update the tf_port-style formal-list scan
// state for one step. Shared by ParseCovergroupFormalList and
// ParseSampleFormalList; the per-list behaviors (what to do when a formal name
// is flushed, and which directions to reject) are supplied as callbacks.
// pending_loc is always recorded on the identifier branch; callers that do not
// need it simply ignore the field.
void Parser::StepTfPortFormalScan(
    TfPortFormalScan& st, const std::function<void()>& flush,
    const std::function<bool()>& reject_direction) {
  if (Check(TokenKind::kLParen)) {
    ++st.depth;
  } else if (Check(TokenKind::kRParen)) {
    --st.depth;
    if (st.depth == 0) flush();
  } else if (reject_direction()) {
    // diagnostic emitted; nothing else to record for this token.
  } else if (st.depth == 1 && Check(TokenKind::kComma)) {
    flush();
  } else if (st.depth == 1 && Check(TokenKind::kEq)) {
    // Everything up to the next comma is a default-value expression whose
    // identifiers are not formal-argument names.
    st.in_default = true;
  } else if (!st.in_default && Check(TokenKind::kIdentifier)) {
    st.pending = CurrentToken().text;
    st.pending_loc = CurrentLoc();
    st.have_pending = true;
  }
}

void Parser::ParseCovergroupFormalList(std::vector<std::string>& names) {
  // Scan across the covergroup's optional formal-argument list, which follows
  // the same balanced-parenthesis shape as a tf_port_list. While scanning,
  // reject any formal declared with output or inout direction, which is not
  // permitted for a covergroup formal (LRM 19.3), and collect each formal's
  // name. In a tf_port the declared name is the last identifier that appears
  // before a comma, a default-value '=', or the closing parenthesis.
  TfPortFormalScan st;
  auto flush = [&]() {
    if (st.have_pending) names.emplace_back(st.pending);
    st.have_pending = false;
    st.in_default = false;
  };
  auto reject_output_inout = [&]() {
    if (!Check(TokenKind::kKwOutput) && !Check(TokenKind::kKwInout))
      return false;
    diag_.Error(CurrentLoc(),
                "a covergroup formal argument cannot be declared 'output' "
                "or 'inout'",
                Subclause("19.3"));
    return true;
  };
  while (st.depth > 0 && !AtEnd()) {
    StepTfPortFormalScan(st, flush, reject_output_inout);
    if (st.depth > 0) Consume();
  }
  if (Check(TokenKind::kRParen)) Consume();
}

// §19.8.1: a sample method formal shares the covergroup argument scope, so a
// name appearing in both the covergroup formal list and the sample formal list
// is illegal. Returns true when the pending sample formal name reuses one of
// the covergroup formal-argument names. Free of Parser state so it stays out of
// the caller's cognitive-complexity budget.
static bool ReusesCovergroupFormal(
    const std::vector<std::string>& covergroup_formals,
    std::string_view pending) {
  for (const auto& formal : covergroup_formals) {
    if (formal == pending) return true;
  }
  return false;
}

void Parser::ParseSampleFormalList(
    const std::vector<std::string>& covergroup_formals,
    std::vector<std::string>& sample_names) {
  // Scan across the formal-argument list of an overridden sample method
  // (introduced by "with function sample"). LRM 19.8.1 places two constraints
  // on these formals that are checked here: a sample formal shall not designate
  // an output direction, and because the sample formals share the covergroup's
  // argument scope (the formals consumed by the covergroup new operator), a
  // name shall not be specified in both the covergroup and sample lists. The
  // collected sample-formal names are handed back so the covergroup body scan
  // can enforce that a sample formal is only referenced in a legal context.
  TfPortFormalScan st;
  auto flush = [&]() {
    if (st.have_pending) {
      sample_names.emplace_back(st.pending);
      if (ReusesCovergroupFormal(covergroup_formals, st.pending)) {
        diag_.Error(st.pending_loc,
                    "sample method formal argument '" +
                        std::string(st.pending) +
                        "' shares the covergroup argument scope and cannot "
                        "reuse a covergroup formal-argument name",
                    Subclause("19.8.1"));
      }
    }
    st.have_pending = false;
    st.in_default = false;
  };
  auto reject_output_inout = [&]() {
    if (!Check(TokenKind::kKwOutput) && !Check(TokenKind::kKwInout))
      return false;
    diag_.Error(CurrentLoc(),
                "a sample method formal argument cannot designate an output "
                "direction",
                Subclause("19.8.1"));
    return true;
  };
  while (st.depth > 0 && !AtEnd()) {
    StepTfPortFormalScan(st, flush, reject_output_inout);
    if (st.depth > 0) Consume();
  }
  if (Check(TokenKind::kRParen)) Consume();
}

// Reports a port list or a coverage event written on a derived covergroup.
// A.2.11 gives covergroup_declaration two alternatives, and the second,
// `covergroup extends covergroup_identifier ;`, ends at the semicolon: the
// optional `( tf_port_list )` and `coverage_event` belong to the first
// alternative alone. §19.4.1 (printed page 581) says why the derived one needs
// neither: "If the base covergroup has a list of arguments specified, the
// derived covergroup implicitly has the same list of arguments", and "If the
// base covergroup has a coverage event specified, the derived covergroup shall
// use that coverage event." The token is left where it stands, so the shared
// tail of Parser::ParseCovergroupDecl consumes it and one report covers the
// whole declaration.
void Parser::RejectDerivedCovergroupTail() {
  if (Check(TokenKind::kLParen) || Check(TokenKind::kAt) ||
      Check(TokenKind::kAtAt) || Check(TokenKind::kKwWith)) {
    diag_.Error(CurrentLoc(),
                "a covergroup that extends a base declares no port list and no "
                "coverage event; it inherits the base's",
                Subclause("A.2.11"));
  }
}

// Reports an `extends` written after a covergroup has named itself. A.2.11's
// first alternative names the covergroup and carries no `extends`, and its
// second carries `extends` and names nothing of its own; no alternative does
// both, so a name followed by `extends` is a production the grammar does not
// have. The base is read and discarded rather than recorded, because §19.4.1
// (printed page 580) gives the derived covergroup the base's own name -- "a
// derived covergroup with name covergroup_identifier is defined" -- and says
// nothing about what a fresh one would mean.
void Parser::RejectNamedCovergroupExtends() {
  if (!Check(TokenKind::kKwExtends)) return;
  diag_.Error(CurrentLoc(),
              "a covergroup that declares its own name cannot also extend a "
              "base; a derived covergroup is written 'covergroup extends "
              "base;'",
              Subclause("A.2.11"));
  Consume();
  ExpectIdentifier(Subclause("19.4.1"));
}

void Parser::ParseCovergroupDecl(std::vector<ModuleItem*>& items) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kCovergroupDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwCovergroup, Subclause("19.3"));

  if (Check(TokenKind::kKwExtends)) {
    // §19.4.1 embedded covergroup inheritance: the derived covergroup is
    // written `covergroup extends base ;` with no fresh name of its own. The
    // covergroup_identifier that follows `extends` names the base covergroup,
    // and the derived covergroup takes that same name so every reference to it
    // resolves to the derived instance.
    Consume();
    auto base = Expect(TokenKind::kIdentifier, Subclause("19.4.1"));
    item->name = base.text;
    item->covergroup_extends_base = base.text;
    RejectDerivedCovergroupTail();
  } else {
    item->name = Expect(TokenKind::kIdentifier, Subclause("19.3")).text;
    RejectNamedCovergroupExtends();
  }

  known_types_.insert(item->name);

  std::vector<std::string> covergroup_formals;
  std::vector<std::string> sample_formals;
  if (Check(TokenKind::kLParen)) {
    Consume();
    ParseCovergroupFormalList(covergroup_formals);
  }

  if (Match(TokenKind::kAt)) {
    Expect(TokenKind::kLParen, Subclause("19.3"));
    ParseEventList();
    Expect(TokenKind::kRParen, Subclause("19.3"));
  } else if (Check(TokenKind::kAtAt)) {
    Consume();
    Expect(TokenKind::kLParen, Subclause("19.3"));
    ParseBlockEventExpression();
    Expect(TokenKind::kRParen, Subclause("19.3"));
  } else if (Match(TokenKind::kKwWith)) {
    Expect(TokenKind::kKwFunction, Subclause("19.8.1"));
    auto sample_id = ExpectIdentifier(Subclause("19.8.1"));
    if (sample_id.text != "sample") {
      diag_.Error(
          sample_id.loc,
          "expected 'sample', got '" + std::string(sample_id.text) + "'",
          Subclause("19.3"));
    }
    Expect(TokenKind::kLParen, Subclause("19.8.1"));
    ParseSampleFormalList(covergroup_formals, sample_formals);
  }
  Expect(TokenKind::kSemicolon, Subclause("19.3"));

  // §19.7: assigning a value to the same coverage option more than once within
  // the same covergroup definition is an error. Track the covergroup-level
  // option assignments seen so far so a repeat can be diagnosed.
  std::unordered_set<std::string> seen_options;
  while (!Check(TokenKind::kKwEndgroup) && !AtEnd()) {
    SkipCovergroupItem(sample_formals, seen_options);
  }
  Expect(TokenKind::kKwEndgroup, Subclause("19.3"));
  MatchEndLabel(item->name);
  items.push_back(item);
}

// §19.8.1: a sample method formal may only designate a coverpoint or a
// conditional guard expression; it shall be an error to use one in any other
// context. A coverage-option assignment (option.* / type_option.*) is such a
// prohibited context, matching the LRM's own error example where a sample
// formal appears on the right-hand side of an option assignment. Scan the
// value expression -- only identifiers to the right of the assignment '=' can
// name a formal, so the option's own name and member on the left are ignored
// -- and flag any reference to a sample formal. The terminating ';' is
// consumed on exit, mirroring SkipToSemiOrEnd.
// §19.8.1: an overridden sample method's formal may only designate a coverpoint
// or conditional guard expression, never a coverage-option value.
static void RejectSampleFormalInOptionValue(
    DiagEngine& diag, const Token& t,
    const std::vector<std::string>& sample_formals) {
  for (const auto& formal : sample_formals) {
    if (formal == t.text) {
      diag.Error(t.loc,
                 "sample method formal argument '" + std::string(t.text) +
                     "' may only designate a coverpoint or "
                     "conditional guard expression, not a "
                     "coverage-option value",
                 Subclause("19.8.1"));
      return;
    }
  }
}

static void ScanOptionForSampleFormalUse(
    Lexer& lexer, DiagEngine& diag,
    const std::vector<std::string>& sample_formals) {
  bool past_assign = false;
  while (!lexer.Peek().Is(TokenKind::kSemicolon) &&
         !lexer.Peek().Is(TokenKind::kKwEndgroup) &&
         !lexer.Peek().Is(TokenKind::kEof)) {
    Token t = lexer.Peek();
    if (t.Is(TokenKind::kEq)) {
      past_assign = true;
    } else if (past_assign && t.Is(TokenKind::kIdentifier)) {
      RejectSampleFormalInOptionValue(diag, t, sample_formals);
    }
    lexer.Next();
  }
  if (lexer.Peek().Is(TokenKind::kSemicolon)) lexer.Next();
}

static bool IsCoverpointOrCross(TokenKind tk) {
  return tk == TokenKind::kKwCoverpoint || tk == TokenKind::kKwCross;
}

static void SkipToSemiOrEnd(Lexer& lexer, TokenKind end_kw) {
  while (!lexer.Peek().Is(TokenKind::kSemicolon) && !lexer.Peek().Is(end_kw) &&
         !lexer.Peek().Is(TokenKind::kEof)) {
    lexer.Next();
  }
  if (lexer.Peek().Is(TokenKind::kSemicolon)) lexer.Next();
}

// §19.7: a covergroup-level coverage-option assignment has the form
// `option . member_name = expression ;`. Assigning the same option twice in the
// same covergroup definition is an error, so each assignment is keyed by its
// `option`/`type_option` keyword joined with the member name and a repeat is
// flagged. §19.8.1: an overridden sample method's formal may not be referenced
// from a coverage-option assignment, so when the covergroup has such formals
// the option value is scanned for an illegal reference rather than skipped.
void Parser::SkipCovergroupOptionAssignment(
    const std::vector<std::string>& sample_formals,
    std::unordered_set<std::string>& seen_options) {
  std::string keyword(CurrentToken().text);
  std::optional<Token> member = ReadCoverageOptionMember(lexer_, diag_);
  if (member) {
    std::string option_name = keyword + '.' + std::string(member->text);
    if (!seen_options.insert(option_name).second) {
      diag_.Error(member->loc,
                  "coverage option '" + option_name +
                      "' is assigned more than once in the same covergroup "
                      "definition",
                  Subclause("19.7"));
    }
  }
  if (sample_formals.empty()) {
    SkipToSemiOrEnd(lexer_, TokenKind::kKwEndgroup);
  } else {
    ScanOptionForSampleFormalUse(lexer_, diag_, sample_formals);
  }
}

// A.2.11's coverage_spec_or_option opens both of its alternatives with
// `{ attribute_instance }`, and cover_point's label may be preceded by a
// data_type_or_implicit, so both are read before the item is told apart by
// its first token. An identifier followed by ':' is the label itself, and is
// asked about first because a name a typedef has declared can label a
// coverpoint as well as type one.
void Parser::SkipCovergroupItem(const std::vector<std::string>& sample_formals,
                                std::unordered_set<std::string>& seen_options) {
  ParseAttributes();

  if (Check(TokenKind::kIdentifier) && IsOptionKeyword(CurrentToken().text)) {
    SkipCovergroupOptionAssignment(sample_formals, seen_options);
    return;
  }

  if (IsCoverpointOrCross(CurrentToken().kind)) {
    SkipUnlabelledCoverpointItem();
    return;
  }

  if (Check(TokenKind::kIdentifier) && IdentifierOpensCoverageLabel()) {
    SkipLabelledCoverpointItem();
    return;
  }

  if (AtDataTypeOrVoid()) {
    ParseCoverpointDataType();
    SkipLabelledCoverpointItem();
    return;
  }

  SkipToSemiOrEnd(lexer_, TokenKind::kKwEndgroup);
}

// True where the identifier the parse stands on is followed by ':', the shape
// of a cover_point_identifier or cross_identifier label rather than of a type
// name before one.
bool Parser::IdentifierOpensCoverageLabel() {
  auto saved = lexer_.SavePos();
  Consume();
  bool labelled = Check(TokenKind::kColon);
  lexer_.RestorePos(saved);
  return labelled;
}

// Reads the data_type_or_implicit before a cover_point's label. A.2.2.1 gives
// it as a data_type or an implicit_data_type, `[ signing ] { packed_dimension
// }`; ParseDataType reads the first and a leading signing, and a bare packed
// dimension is what it leaves standing.
void Parser::ParseCoverpointDataType() {
  DataType dtype = ParseDataType();
  if (Check(TokenKind::kLBracket)) ParsePackedDims(dtype);
}

// §19.5/§19.6: a coverpoint or cross written without a label.
void Parser::SkipUnlabelledCoverpointItem() {
  bool is_cross = Check(TokenKind::kKwCross);
  Consume();
  if (is_cross) {
    ValidateCrossItemList();
    ParseCoverageIffGuard();
  } else {
    ParseCoverpointHead();
  }
  SkipCoverpointBody(
      lexer_, diag_,
      is_cross ? CovItemLevel::kCross : CovItemLevel::kCoverpoint);
}

// §19.5/§19.6: a `label : coverpoint`/`label : cross` item. An identifier that
// turns out not to introduce either is skipped as a plain coverpoint body.
void Parser::SkipLabelledCoverpointItem() {
  Consume();
  CovItemLevel level = CovItemLevel::kCoverpoint;
  if (Match(TokenKind::kColon) && IsCoverpointOrCross(CurrentToken().kind)) {
    if (Check(TokenKind::kKwCross)) level = CovItemLevel::kCross;
    Consume();
    if (level == CovItemLevel::kCross) {
      ValidateCrossItemList();
      ParseCoverageIffGuard();
    } else {
      ParseCoverpointHead();
    }
  }
  SkipCoverpointBody(lexer_, diag_, level);
}

// Reads what A.2.11's cover_point puts after the `coverpoint` keyword,
// `expression [ iff ( expression ) ]`. §19.3 (printed page 577) has "a
// coverage point can cover a variable or an expression", and a coverpoint
// written with nothing to cover is reported where its expression was due.
void Parser::ParseCoverpointHead() {
  if (Check(TokenKind::kSemicolon) || Check(TokenKind::kLBrace) ||
      Check(TokenKind::kKwIff) || Check(TokenKind::kKwEndgroup) || AtEnd()) {
    diag_.Error(CurrentLoc(),
                "a coverpoint covers an expression; none is written",
                Subclause("A.2.11"));
  } else {
    ParseExpr();
  }
  ParseCoverageIffGuard();
}

// Reads the `[ iff ( expression ) ]` that A.2.11 puts after a cover_point's
// expression and after a cover_cross's list_of_cross_items: the guard's
// expression is parenthesized in both, and one written bare is reported at
// the token where its '(' was due and read on to where the item's body or
// terminator resumes.
void Parser::ParseCoverageIffGuard() {
  if (!Match(TokenKind::kKwIff)) return;
  if (Match(TokenKind::kLParen)) {
    ParseExpr();
    Expect(TokenKind::kRParen, Subclause("A.2.11"));
    return;
  }
  diag_.Error(CurrentLoc(),
              "a coverage guard is written 'iff ( expression )'; its "
              "expression is parenthesized",
              Subclause("A.2.11"));
  if (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kLBrace)) ParseExpr();
}

void Parser::ValidateCrossItemList() {
  // §19.6 / Syntax 19-4: list_of_cross_items ::= cross_item , cross_item
  // { , cross_item }, where cross_item ::= cover_point_identifier |
  // variable_identifier. The list ends at the optional `iff` guard, the cross
  // body `{`, or the terminating `;`. A cross must name at least two items and
  // each item must be a bare identifier -- expressions may not appear directly
  // in a cross (a coverage point must be defined first).
  SourceLoc start = CurrentLoc();
  int item_count = 0;
  bool expr_item = false;
  bool expect_item = true;
  while (!AtEnd()) {
    TokenKind k = CurrentToken().kind;
    if (k == TokenKind::kKwIff || k == TokenKind::kLBrace ||
        k == TokenKind::kSemicolon || k == TokenKind::kKwEndgroup) {
      break;
    }
    if (k == TokenKind::kComma) {
      Consume();
      expect_item = true;
      continue;
    }
    if (k == TokenKind::kIdentifier && expect_item) {
      ++item_count;
      Consume();
      expect_item = false;
      continue;
    }
    // Anything else between items (an operator, a select, a second identifier
    // with no separating comma) means a cross item is a compound expression.
    expr_item = true;
    Consume();
  }
  if (expr_item) {
    diag_.Error(
        start,
        "a cross item shall be a coverage point or variable identifier; "
        "an expression cannot be used directly in a cross",
        Subclause("19.6"));
  } else if (item_count < 2) {
    diag_.Error(start, "a cross shall list at least two coverage points",
                Subclause("19.6"));
  }
}

}  // namespace delta
