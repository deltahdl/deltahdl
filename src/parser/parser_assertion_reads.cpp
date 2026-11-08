#include <cstddef>
#include <string_view>
#include <vector>

#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_module.h"
#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"

namespace delta {

namespace {

struct OpenInstance {
  std::string_view callee;
  int depth = 0;
  size_t index = 0;
  size_t tokens = 0;
  Token first;
};

struct AssertionTextScan {
  ModuleItem* item = nullptr;
  Token prev;
  Token prev2;
  int parens = 0;
  int brackets = 0;
  int const_bracket = 0;
  std::vector<OpenInstance> open;
  int braces = 0;
  std::vector<int> patterns;
  bool in_attribute = false;

  void CountArgToken(const Token& t) {
    if (open.empty() || parens < open.back().depth) return;
    OpenInstance& inst = open.back();
    if (inst.tokens++ == 0) inst.first = t;
  }

  void FinishArg() {
    OpenInstance& inst = open.back();
    if (inst.tokens == 1 && inst.first.Is(TokenKind::kIdentifier)) {
      item->assertion_instance_args.push_back(
          {inst.callee, inst.index, inst.first.text, inst.first.loc});
    }
    ++inst.index;
    inst.tokens = 0;
  }

  bool OpensConstBracket(const Token& next) const {
    return prev.Is(TokenKind::kHashHash) || next.Is(TokenKind::kStar) ||
           next.Is(TokenKind::kEq) || next.Is(TokenKind::kArrow) ||
           next.Is(TokenKind::kPlus);
  }

  bool IsPatternKey(const Token& next) const {
    return !patterns.empty() && next.Is(TokenKind::kColon) &&
           (prev.Is(TokenKind::kApostropheLBrace) ||
            prev.Is(TokenKind::kComma));
  }

  void Brace(const Token& t) {
    if (t.Is(TokenKind::kRBrace)) {
      if (!patterns.empty() && patterns.back() == braces) patterns.pop_back();
      --braces;
      return;
    }
    ++braces;
    if (t.Is(TokenKind::kApostropheLBrace)) patterns.push_back(braces);
  }

  void Identifier(const Token& t, const Token& next) {
    if (prev.Is(TokenKind::kDot) || prev.Is(TokenKind::kColonColon) ||
        IsPatternKey(next)) {
      return;
    }
    if (prev.Is(TokenKind::kHashHash)) {
      item->assertion_const_names.push_back(t.text);
      item->assertion_reads.push_back({t.text, t.loc});
      return;
    }
    if (prev.Is(TokenKind::kIdentifier) && !prev2.Is(TokenKind::kDot) &&
        !prev2.Is(TokenKind::kColonColon) && !prev2.Is(TokenKind::kHashHash)) {
      item->assertion_local_names.push_back(t.text);
      return;
    }
    if (next.Is(TokenKind::kIdentifier) || next.Is(TokenKind::kColonColon) ||
        next.Is(TokenKind::kLParen) || next.Is(TokenKind::kApostrophe)) {
      return;
    }
    if (const_bracket > 0) {
      item->assertion_const_names.push_back(t.text);
    }
    item->assertion_reads.push_back({t.text, t.loc, next.Is(TokenKind::kDot)});
  }

  void OpenParen(const Token& t) {
    CountArgToken(t);
    ++parens;
    if (prev.Is(TokenKind::kIdentifier) && !prev2.Is(TokenKind::kDot) &&
        !prev2.Is(TokenKind::kColonColon)) {
      open.push_back({prev.text, parens, 0, 0, {}});
    }
  }

  void CloseParen(const Token& t) {
    if (AtArgListDepth()) {
      if (open.back().index > 0 || open.back().tokens > 0) FinishArg();
      open.pop_back();
    } else {
      CountArgToken(t);
    }
    --parens;
  }

  bool AtArgListDepth() const {
    return !open.empty() && open.back().depth == parens;
  }

  void OtherToken(const Token& t, const Token& next) {
    CountArgToken(t);
    if (t.Is(TokenKind::kLBracket)) {
      ++brackets;
      if (const_bracket == 0 && OpensConstBracket(next)) {
        const_bracket = brackets;
      }
    } else if (t.Is(TokenKind::kRBracket)) {
      if (const_bracket == brackets) const_bracket = 0;
      --brackets;
    } else if (t.Is(TokenKind::kIdentifier)) {
      Identifier(t, next);
    } else if (t.Is(TokenKind::kApostropheLBrace) || t.Is(TokenKind::kLBrace) ||
               t.Is(TokenKind::kRBrace)) {
      Brace(t);
    }
  }

  void Step(const Token& t, const Token& next) {
    if (in_attribute || t.Is(TokenKind::kAttrStart)) {
      in_attribute = !t.Is(TokenKind::kAttrEnd);
      return;
    }
    if (t.Is(TokenKind::kLParen)) {
      OpenParen(t);
    } else if (t.Is(TokenKind::kRParen)) {
      CloseParen(t);
    } else if (t.Is(TokenKind::kComma) && AtArgListDepth()) {
      FinishArg();
    } else {
      OtherToken(t, next);
    }
    prev2 = prev;
    prev = t;
  }
};

}  // namespace

void ParserPropertySpecHelpers::RecordAssertionReads(Parser& p,
                                                     ModuleItem* item,
                                                     TokenKind end) {
  auto saved = p.lexer_.SavePos();
  AssertionTextScan scan;
  scan.item = item;
  while (true) {
    Token t = p.lexer_.Peek();
    if (t.IsEof()) break;
    if (t.Is(end) && (end != TokenKind::kRParen || scan.parens == 0)) break;
    p.lexer_.Next();
    scan.Step(t, p.lexer_.Peek());
  }
  p.lexer_.RestorePos(saved);
}

}  // namespace delta
