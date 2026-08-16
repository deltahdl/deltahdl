// IEEE 1800-2023 §8.20's dynamic override specifiers: the `:initial`,
// `:extends` and `:final` that may stand between a method's `function` or
// `task` keyword and its name.
//
// The order is the grammar's, and the grammar is what a conforming source is
// measured against. `dynamic_override_specifiers ::=
// [ initial_or_extends_specifier ] [ final_specifier ]` is printed twice, in
// Syntax 8-1 (printed page 181) and again in A.2.7 (printed page 1187), and
// Annex A is titled "(normative) Formal syntax". §8.20 Example 3 prints the
// opposite order, `virtual function :final :extends void f2();` under the
// comment "OK: f2 shall not be overridden in subclasses of A" (printed page
// 198), and no sentence in §8.20 or Syntax 8-1 constrains the order either way:
// the clause's rule for the pair, on printed page 197, is "final may be
// combined with either initial or extends", which names no order. The example
// is illustrative and does not derive from the normative production, so the
// production decides and the example is reported rather than followed.
//
// These functions are their own translation unit rather than part of
// src/parser/parser_class.cpp, which they would take to 969 lines, inside the
// band assert-no-oversized-source-files warns at.

#include "parser/parser.h"

namespace delta {

// CPD-dedup: judging one specifier takes the same two questions wherever it
// stands in the sequence, so both are asked in one place here.
struct ParserClassOverrideHelpers {
  // Which specifiers a declaration has read so far. What a specifier is judged
  // against is which of the production's two categories are already taken, not
  // which position it stands in.
  struct OverrideSpecifiers {
    bool initial = false;
    bool extends = false;
    bool has_final = false;
  };

  // Reports `spec` when the production has no room left for it, and answers
  // whether it did. Each category holds one specifier: a second final_specifier
  // and a second initial_or_extends_specifier are both refused. The case of the
  // latter where the two differ is the one §8.20 states in its own words,
  // "initial and extends are mutually exclusive; specifying both in a method
  // declaration shall result in an error", so it keeps the message #3107 gave
  // it. A reported specifier is not recorded, which is what keeps
  // ModuleItem::is_method_initial and ModuleItem::is_method_extends from both
  // ending up true and Elaborator::ValidateOneMethodOverride from being handed
  // a pair the clause forbids.
  static bool RepeatIsReported(Parser& p, const OverrideSpecifiers& seen,
                               TokenKind spec, SourceLoc loc) {
    if (spec == TokenKind::kKwFinal) {
      if (!seen.has_final) return false;
      p.diag_.Error(loc, "a method takes at most one ':final' specifier",
                    Subclause("8.20"));
      return true;
    }
    if (!seen.initial && !seen.extends) return false;
    if (spec == TokenKind::kKwExtends ? seen.initial : seen.extends) {
      p.diag_.Error(loc, "':initial' and ':extends' are mutually exclusive",
                    Subclause("8.20"));
      return true;
    }
    p.diag_.Error(
        loc, "a method takes at most one ':initial' or ':extends' specifier",
        Subclause("8.20"));
    return true;
  }

  // Records `spec`, reporting the order first where an
  // initial_or_extends_specifier follows the final_specifier the production
  // writes after it. Both are still recorded in that case, because each
  // specifier is legal and means what it says and only their order is not;
  // dropping one would hide a second defect in the declaration behind the
  // first.
  static void RecordOverrideSpecifier(Parser& p, OverrideSpecifiers& seen,
                                      ModuleItem* item, TokenKind spec,
                                      SourceLoc loc) {
    if (spec == TokenKind::kKwFinal) {
      seen.has_final = true;
      if (item) item->is_method_final = true;
      return;
    }
    if (seen.has_final) {
      p.diag_.Error(
          loc, "':final' is written after ':initial' or ':extends', not before",
          Subclause("8.20"));
    }
    if (spec == TokenKind::kKwInitial) {
      seen.initial = true;
      if (item) item->is_method_initial = true;
      return;
    }
    seen.extends = true;
    if (item) item->is_method_extends = true;
  }
};

// Whether tk is one of the three keywords a colon introduces in
// `dynamic_override_specifiers`.
static bool IsOverrideSpecifierKeyword(TokenKind tk) {
  return tk == TokenKind::kKwInitial || tk == TokenKind::kKwExtends ||
         tk == TokenKind::kKwFinal;
}

// Reads the specifiers one at a time, which is what lets a report be about the
// sequence. Read in two fixed positions instead, `:final :extends` took `final`
// in the first and left `extends` standing where the name belongs, so
// Parser::ParseFuncName reported the method as having no name under §13.4 and
// said nothing about the order. Every specifier is consumed whatever is wrong
// with it, which is what leaves the name where Parser::ParseFuncName expects
// it.
//
// A colon followed by anything else is left where it stands rather than
// consumed, because the loop would otherwise eat every colon it met.
void Parser::ParseDynamicOverrideSpecifiers(ModuleItem* item) {
  ParserClassOverrideHelpers::OverrideSpecifiers seen;
  while (Check(TokenKind::kColon)) {
    auto saved = lexer_.SavePos();
    Consume();
    TokenKind spec = CurrentToken().kind;
    if (!IsOverrideSpecifierKeyword(spec)) {
      lexer_.RestorePos(saved);
      return;
    }
    auto spec_tok = Consume();
    if (!ParserClassOverrideHelpers::RepeatIsReported(*this, seen, spec,
                                                      spec_tok.loc)) {
      ParserClassOverrideHelpers::RecordOverrideSpecifier(*this, seen, item,
                                                          spec, spec_tok.loc);
    }
  }
}

}  // namespace delta
