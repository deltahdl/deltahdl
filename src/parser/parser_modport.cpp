// The modport declarations of IEEE 1800-2023 §25.5, read inside an interface
// body: the modport's ports with their directions, and the import and export
// of tasks and functions through it. Moved here from parser_class.cpp, which
// the A.1.9 reports on a class item's qualifiers took past the limit
// assert-no-oversized-source-files enforces.

#include <vector>

#include "parser/parser.h"

namespace delta {

// A.2.7 writes task_prototype and function_prototype with
// `[ dynamic_override_specifiers ]` after the keyword, so a modport_tf_port's
// method_prototype may carry one, and the specifiers are read so that the
// name that follows them is found; A.10's footnote 25 has "the
// dynamic_override_specifiers shall only be legal on method declarations
// inside a non-interface class scope", and a modport is no class, so one
// read here is reported at the prototype. The parser reported the prototype
// as a missing identifier at the ':'.
void Parser::ParseModportPrototypeSpecifiers(ModuleItem* item) {
  ParseDynamicOverrideSpecifiers(item);
  if (item->is_method_initial || item->is_method_extends ||
      item->is_method_final) {
    diag_.Error(item->loc,
                "dynamic_override_specifiers shall only be legal on method "
                "declarations inside a non-interface class scope",
                Subclause("8.20"));
  }
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

// One entry of A.2.9's modport_item, either a modport_ports_declaration
// opening with its port_direction, import_export or `clocking`, or a port
// continuing the declaration before it. An entry that opens with none of the
// three where no declaration is open to continue -- the first entry of the
// item, or the one after a modport_clocking_declaration, which is `clocking
// clocking_identifier` and continues with nothing -- is reported under A.2.9
// and read as a simple port of no direction, so that the item's list is read
// to its ')'.
void Parser::ParseModportPortEntry(ModportDecl* mp, ModportScan& scan) {
  using Opened = ModportScan::Opened;
  ParseAttributes();
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
    // A.2.9's modport_item is `modport_identifier ( modport_ports_declaration
    // { , modport_ports_declaration } )`: one declaration at least, and an
    // item written with none is reported where its first was due.
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
