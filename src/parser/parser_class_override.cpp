#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_module.h"
#include "parser/parser.h"

namespace delta {

struct ParserClassOverrideHelpers {
  struct OverrideSpecifiers {
    bool initial = false;
    bool extends = false;
    bool has_final = false;
  };

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

static bool IsOverrideSpecifierKeyword(TokenKind tk) {
  return tk == TokenKind::kKwInitial || tk == TokenKind::kKwExtends ||
         tk == TokenKind::kKwFinal;
}

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
