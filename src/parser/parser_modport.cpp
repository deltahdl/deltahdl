// The modport declarations of IEEE 1800-2023 §25.5, read inside an interface
// body: the modport's ports with their directions, and the import and export
// of tasks and functions through it. Moved here from parser_class.cpp, which
// the A.1.9 reports on a class item's qualifiers took past the limit
// assert-no-oversized-source-files enforces.

#include <vector>

#include "parser/parser.h"

namespace delta {

ModportPort Parser::ParseModportTfPort(bool is_import) {
  ModportPort port;
  port.is_import = is_import;
  port.is_export = !is_import;
  if (Check(TokenKind::kKwTask)) {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kTaskDecl;
    item->loc = CurrentLoc();
    Consume();
    item->name = Expect(TokenKind::kIdentifier, Subclause("25.5")).text;
    if (Check(TokenKind::kLParen)) item->func_args = ParseFunctionArgs(false);
    port.prototype = item;
    port.name = item->name;
  } else if (Check(TokenKind::kKwFunction)) {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kFunctionDecl;
    item->loc = CurrentLoc();
    Consume();
    item->data_type = ParseFunctionReturnType();
    item->name = Expect(TokenKind::kIdentifier, Subclause("25.5")).text;
    if (Check(TokenKind::kLParen)) item->func_args = ParseFunctionArgs(false);
    port.prototype = item;
    port.name = item->name;
  } else {
    port.name = Expect(TokenKind::kIdentifier, Subclause("25.5")).text;
  }
  return port;
}

ModportPort Parser::ParseModportSimplePort(Direction dir) {
  ModportPort port;
  port.direction = dir;
  if (Match(TokenKind::kDot)) {
    port.is_named_port = true;
    port.name = Expect(TokenKind::kIdentifier, Subclause("25.5.4")).text;
    Expect(TokenKind::kLParen, Subclause("25.5.4"));
    if (!Check(TokenKind::kRParen)) port.expr = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("25.5.4"));
  } else {
    port.name = Expect(TokenKind::kIdentifier, Subclause("25.5")).text;
  }
  return port;
}

static Direction TokenToDirection(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwInput:
      return Direction::kInput;
    case TokenKind::kKwOutput:
      return Direction::kOutput;
    case TokenKind::kKwInout:
      return Direction::kInout;
    case TokenKind::kKwRef:
      return Direction::kRef;
    default:
      return Direction::kNone;
  }
}

void Parser::ParseModportPortEntry(ModportDecl* mp, Direction& cur_dir,
                                   int& tf_mode) {
  ParseAttributes();
  if (Check(TokenKind::kKwClocking)) {
    tf_mode = 0;
    Consume();
    ModportPort port;
    port.is_clocking = true;
    port.name = Expect(TokenKind::kIdentifier, Subclause("25.5.5")).text;
    mp->ports.push_back(port);
  } else if (Check(TokenKind::kKwImport) || Check(TokenKind::kKwExport)) {
    tf_mode = Check(TokenKind::kKwImport) ? 1 : 2;
    Consume();
    mp->ports.push_back(ParseModportTfPort(tf_mode == 1));
  } else if (IsPortDirection(CurrentToken().kind)) {
    tf_mode = 0;
    cur_dir = TokenToDirection(CurrentToken().kind);
    Consume();
    mp->ports.push_back(ParseModportSimplePort(cur_dir));
  } else if (tf_mode != 0) {
    mp->ports.push_back(ParseModportTfPort(tf_mode == 1));
  } else {
    mp->ports.push_back(ParseModportSimplePort(cur_dir));
  }
}

void Parser::ParseModportItem(ModportDecl* mp) {
  Direction cur_dir = Direction::kNone;
  int tf_mode = 0;
  while (!Check(TokenKind::kRParen) && !AtEnd()) {
    auto before = lexer_.SavePos().pos;
    ParseModportPortEntry(mp, cur_dir, tf_mode);
    if (!Check(TokenKind::kRParen))
      Expect(TokenKind::kComma, Subclause("25.5"));
    // Missing ')': a token that is neither a port nor a comma (e.g. the
    // terminating ';') leaves the cursor unmoved. Stop so the caller's
    // Expect(kRParen) reports the error instead of spinning.
    if (lexer_.SavePos().pos == before) break;
  }
}

void Parser::ParseModportDecl(std::vector<ModportDecl*>& out) {
  Expect(TokenKind::kKwModport, Subclause("25.5"));
  do {
    auto* mp = arena_.Create<ModportDecl>();
    mp->loc = CurrentLoc();
    mp->name = Expect(TokenKind::kIdentifier, Subclause("25.5")).text;
    Expect(TokenKind::kLParen, Subclause("25.5"));
    ParseModportItem(mp);
    Expect(TokenKind::kRParen, Subclause("25.5"));
    out.push_back(mp);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon, Subclause("25.5"));
}

}  // namespace delta
