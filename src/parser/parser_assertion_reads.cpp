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

// One instance's parenthesized argument list open at `depth`: the name of what
// it instantiates, the position of the argument being read, how many tokens
// that argument has, and the first of them.
struct OpenInstance {
  std::string_view callee;
  int depth = 0;
  size_t index = 0;
  size_t tokens = 0;
  Token first;
};

// The token-level state of the scan: the tokens before the current one, the
// parenthesis depth, the instances whose argument lists are open, the depth
// of the cycle delay or repetition bracket the scan stands in, zero where it
// stands in none, and how many braces are open, with the depth at which each
// open assignment pattern (§10.9) opened.
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

  void CountArgToken(const Token& t) {
    if (open.empty() || parens < open.back().depth) return;
    OpenInstance& inst = open.back();
    if (inst.tokens++ == 0) inst.first = t;
  }

  // §16.8: an argument written as one identifier alone is recorded against
  // the instance's formal at its position.
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

  // §10.9.2: a member key of an assignment pattern, written first or after a
  // comma and followed by its colon, names a member of the pattern's type,
  // no object of the scope.
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
    // The count of a cycle delay, `x ##delay1 y`, is read whatever follows.
    if (prev.Is(TokenKind::kHashHash)) {
      item->assertion_const_names.push_back(t.text);
      item->assertion_reads.push_back({t.text, t.loc});
      return;
    }
    // A type name followed by the name it declares, `st_t v;`: the second
    // is a local variable of the declaration. The operand after a delay
    // count, `##delay1 y`, is no such name.
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
    item->assertion_reads.push_back({t.text, t.loc});
  }

  // An opening parenthesis after a name, not a member's, opens the argument
  // list of an instance or a call written with that name.
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

// §23.9, §16.8 and §16.10: a scan of the text from the current token to `end`
// (for `kRParen`, the one closing the parenthesis the caller consumed), which
// records on `item` the names the text reads without a hierarchical path, the
// names it declares as local variables of a user-defined type, the names it
// writes in a cycle delay or a repetition bound, and the identifiers it passes
// whole as positional actuals to the instances it writes. A name followed by
// an argument list is an instance or a call, which other rules resolve, and a
// name after `.` or `::` is a member, which the path resolves. The lexer is
// left where it was.
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
