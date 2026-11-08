#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "parser/override_specifier_placement.h"
#include "parser/parser.h"
#include "parser/parser_prototype_validate.h"
#include "parser/parser_token_skips.h"

namespace delta {

void Parser::ParseModportPrototypeSpecifiers(ModuleItem* item) {
  ParseDynamicOverrideSpecifiers(item);
  ReportMisplacedOverrideSpecifiers(*item, diag_);
}

ModportPort Parser::ParseModportTfPort(bool is_import) {
  ModportPort port;
  port.is_import = is_import;
  port.is_export = !is_import;
  if (Check(TokenKind::kKwTask)) {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kTaskDecl;
    item->loc = CurrentLoc();
    Consume();
    ParseModportPrototypeSpecifiers(item);
    item->name = Expect(TokenKind::kIdentifier, Subclause("25.5")).text;
    if (Check(TokenKind::kLParen)) item->func_args = ParseFunctionArgs(false);
    port.prototype = item;
    port.name = item->name;
  } else if (Check(TokenKind::kKwFunction)) {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kFunctionDecl;
    item->loc = CurrentLoc();
    Consume();
    ParseModportPrototypeSpecifiers(item);
    item->data_type = ParseFunctionReturnType();
    if (IsImplicitResultType(item->data_type)) {
      diag_.Error(item->loc,
                  "a modport's function prototype writes its result type out, "
                  "a data type or void",
                  Subclause("A.2.9"));
    }
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

void Parser::ParseModportPortEntry(ModportDecl* mp, ModportScan& scan) {
  using Opened = ModportScan::Opened;
  const SourceLoc kAttrLoc = CurrentLoc();
  const bool kAttributed = !ParseAttributes().empty();
  if (Check(TokenKind::kKwClocking)) {
    scan.opened = Opened::kClocking;
    Consume();
    ModportPort port;
    port.is_clocking = true;
    port.name = Expect(TokenKind::kIdentifier, Subclause("25.5.5")).text;
    mp->ports.push_back(port);
    return;
  }
  if (Check(TokenKind::kKwImport) || Check(TokenKind::kKwExport)) {
    scan.opened = Opened::kTf;
    scan.is_import = Check(TokenKind::kKwImport);
    Consume();
    mp->ports.push_back(ParseModportTfPort(scan.is_import));
    return;
  }
  if (IsPortDirection(CurrentToken().kind)) {
    scan.opened = Opened::kSimple;
    scan.dir = TokenToDirection(CurrentToken().kind);
    Consume();
    mp->ports.push_back(ParseModportSimplePort(scan.dir));
    return;
  }
  if (kAttributed &&
      (scan.opened == Opened::kSimple || scan.opened == Opened::kTf)) {
    diag_.Error(kAttrLoc,
                "an attribute instance opens a modport_ports_declaration, and "
                "a port continuing one takes none",
                Subclause("A.2.9"));
  }
  if (scan.opened == Opened::kTf) {
    mp->ports.push_back(ParseModportTfPort(scan.is_import));
    return;
  }
  if (scan.opened != Opened::kSimple) {
    diag_.Error(CurrentLoc(),
                "a modport_ports_declaration opens with a port_direction, "
                "'import', 'export' or 'clocking'",
                Subclause("A.2.9"));
    scan.dir = Direction::kNone;
  }
  mp->ports.push_back(ParseModportSimplePort(scan.dir));
}

void Parser::ParseModportItem(ModportDecl* mp) {
  ModportScan scan;
  while (!Check(TokenKind::kRParen) && !AtEnd()) {
    auto before = lexer_.SavePos().pos;
    ParseModportPortEntry(mp, scan);
    if (!Check(TokenKind::kRParen))
      Expect(TokenKind::kComma, Subclause("25.5"));
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
    if (mp->ports.empty()) {
      diag_.Error(CurrentLoc(),
                  "a modport item has at least one modport_ports_declaration",
                  Subclause("A.2.9"));
    }
    Expect(TokenKind::kRParen, Subclause("25.5"));
    out.push_back(mp);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon, Subclause("25.5"));
}

}  // namespace delta
