#include <optional>

#include "common/types.h"
#include "parser/parser.h"

namespace delta {

static Direction TokenToDirection(TokenKind kind) {
  switch (kind) {
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

ModuleItem* Parser::ParseImportItem() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kImportDecl;
  item->loc = CurrentLoc();
  item->import_item.package_name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kColonColon);
  if (Match(TokenKind::kStar)) {
    item->import_item.is_wildcard = true;
  } else {
    item->import_item.item_name = Expect(TokenKind::kIdentifier).text;
  }
  return item;
}

void Parser::ParseImportDecl(std::vector<ModuleItem*>& items) {
  Expect(TokenKind::kKwImport);
  // DPI-C import: import "DPI-C" ...
  if (Check(TokenKind::kStringLiteral)) {
    items.push_back(ParseDpiImport());
    return;
  }
  items.push_back(ParseImportItem());
  while (Match(TokenKind::kComma)) {
    items.push_back(ParseImportItem());
  }
  Expect(TokenKind::kSemicolon);
}

void Parser::ParseExportDecl(std::vector<ModuleItem*>& items) {
  auto loc = CurrentLoc();
  Expect(TokenKind::kKwExport);
  // DPI-C export: export "DPI-C" ...
  if (Check(TokenKind::kStringLiteral)) {
    items.push_back(ParseDpiExport(loc));
    return;
  }
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kExportDecl;
  item->loc = loc;
  if (Match(TokenKind::kStar)) {
    // export *::*;
    item->import_item.package_name = "*";
    Expect(TokenKind::kColonColon);
    Expect(TokenKind::kStar);
    item->import_item.is_wildcard = true;
  } else {
    item->import_item.package_name = Expect(TokenKind::kIdentifier).text;
    Expect(TokenKind::kColonColon);
    if (Match(TokenKind::kStar)) {
      item->import_item.is_wildcard = true;
    } else {
      item->import_item.item_name = Expect(TokenKind::kIdentifier).text;
    }
  }
  items.push_back(item);
  // A.2.1.3: export package_import_item { , package_import_item } ;
  while (Match(TokenKind::kComma)) {
    auto* next = arena_.Create<ModuleItem>();
    next->kind = ModuleItemKind::kExportDecl;
    next->loc = loc;
    next->import_item.package_name = Expect(TokenKind::kIdentifier).text;
    Expect(TokenKind::kColonColon);
    if (Match(TokenKind::kStar)) {
      next->import_item.is_wildcard = true;
    } else {
      next->import_item.item_name = Expect(TokenKind::kIdentifier).text;
    }
    items.push_back(next);
  }
  Expect(TokenKind::kSemicolon);
}

ModuleItem* Parser::ParseDpiImport() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kDpiImport;
  item->loc = CurrentLoc();
  Consume();  // string literal "DPI-C"

  // Optional: pure or context
  if (Match(TokenKind::kKwPure)) {
    item->dpi_is_pure = true;
  }
  if (Match(TokenKind::kKwContext)) {
    item->dpi_is_context = true;
  }

  // Optional: c_identifier = (lookahead for identifier followed by '=')
  if (Check(TokenKind::kIdentifier)) {
    auto saved = lexer_.SavePos();
    auto tok = Consume();
    if (Match(TokenKind::kEq)) {
      item->dpi_c_name = tok.text;
    } else {
      lexer_.RestorePos(saved);
    }
  }

  // function or task
  if (Match(TokenKind::kKwTask)) {
    item->dpi_is_task = true;
  } else {
    Expect(TokenKind::kKwFunction);
  }

  // Parse return type (for functions) and name
  if (!item->dpi_is_task) {
    item->return_type = ParseDataType();
  }
  item->name = Expect(TokenKind::kIdentifier).text;

  // Optional argument list
  if (Check(TokenKind::kLParen)) {
    item->func_args = ParseFunctionArgs();
  }
  Expect(TokenKind::kSemicolon);
  return item;
}

ModuleItem* Parser::ParseDpiExport(SourceLoc loc) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kDpiExport;
  item->loc = loc;
  Consume();  // string literal "DPI-C"

  // Optional: c_identifier =
  if (Check(TokenKind::kIdentifier)) {
    auto saved = lexer_.SavePos();
    auto tok = Consume();
    if (Match(TokenKind::kEq)) {
      item->dpi_c_name = tok.text;
    } else {
      lexer_.RestorePos(saved);
    }
  }

  // function or task
  if (Match(TokenKind::kKwTask)) {
    item->dpi_is_task = true;
  } else {
    Expect(TokenKind::kKwFunction);
  }
  item->name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kSemicolon);
  return item;
}

void Parser::ParseParamPortDecl(
    std::vector<std::pair<std::string_view, Expr*>>& params) {
  Match(TokenKind::kKwParameter) || Match(TokenKind::kKwLocalparam);
  // Handle type parameter: #(type T = real)  (§6.20.3)
  if (Match(TokenKind::kKwType)) {
    auto name = Expect(TokenKind::kIdentifier);
    if (Match(TokenKind::kEq)) {
      if (Check(TokenKind::kKwType)) {
        ParseExpr();  // type() expression as default
      } else {
        ParseDataType();  // consume default type
      }
    }
    params.push_back({name.text, nullptr});
    known_types_.insert(name.text);
    return;
  }
  ParseDataType();  // consume optional type (not stored in params)
  auto name = Expect(TokenKind::kIdentifier);
  Expr* default_val = nullptr;
  if (Match(TokenKind::kEq)) {
    default_val = ParseExpr();
  }
  params.push_back({name.text, default_val});
}

void Parser::ParseParamsPortsAndSemicolon(ModuleDecl& decl) {
  // Optional package imports in module header (§26.4)
  while (Check(TokenKind::kKwImport)) {
    ParseImportDecl(decl.items);
  }
  if (Check(TokenKind::kHash)) {
    Consume();
    Expect(TokenKind::kLParen);
    if (!Check(TokenKind::kRParen)) {
      ParseParamPortDecl(decl.params);
      while (Match(TokenKind::kComma)) {
        ParseParamPortDecl(decl.params);
      }
    }
    Expect(TokenKind::kRParen);
  }
  if (Check(TokenKind::kLParen)) {
    ParsePortList(decl);
  }
  Expect(TokenKind::kSemicolon);
}

void Parser::ParsePortList(ModuleDecl& mod) {
  Expect(TokenKind::kLParen);
  if (Check(TokenKind::kRParen)) {
    Consume();
    return;
  }
  // (.* ) wildcard port form (A.1.2)
  if (Check(TokenKind::kDotStar)) {
    Consume();
    mod.has_wildcard_ports = true;
    Expect(TokenKind::kRParen);
    return;
  }
  // Detect non-ANSI style: first token is an identifier (no direction).
  if (CheckIdentifier()) {
    ParseNonAnsiPortList(mod);
    return;
  }
  mod.ports.push_back(ParsePortDecl());
  while (Match(TokenKind::kComma)) {
    mod.ports.push_back(ParsePortDecl());
  }
  Expect(TokenKind::kRParen);
}

void Parser::ParseNonAnsiPortList(ModuleDecl& mod) {
  // Non-ANSI: module m(a, b, c); -- just identifier names.
  do {
    PortDecl port;
    port.loc = CurrentLoc();
    port.name = ExpectIdentifier().text;
    mod.ports.push_back(port);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kRParen);
}

PortDecl Parser::ParsePortDecl() {
  PortDecl port;
  port.loc = CurrentLoc();

  Direction dir = TokenToDirection(CurrentToken().kind);
  if (dir != Direction::kNone) {
    port.direction = dir;
    Consume();
  }

  // A.2.1.2: variable_port_type ::= var_data_type
  // var_data_type ::= data_type | var data_type_or_implicit
  if (Match(TokenKind::kKwVar)) {
    port.data_type = ParseDataType();
    // §6.8: implicit_data_type — bare packed dims after 'var'
    if (port.data_type.kind == DataTypeKind::kImplicit &&
        Check(TokenKind::kLBracket)) {
      ParsePackedDims(port.data_type);
    }
    if (port.data_type.kind == DataTypeKind::kImplicit) {
      port.data_type.kind = DataTypeKind::kLogic;
    }
  } else {
    port.data_type = ParseDataType();
  }

  // Handle implicit type with packed dims: input [3:0] a (§6.10)
  // Also handles signing already parsed: input signed [7:0] a (A.2.2.1)
  if (port.data_type.kind == DataTypeKind::kImplicit) {
    if (port.data_type.packed_dim_left) {
      // Packed dims already parsed by ParseDataType (signing path)
      port.data_type.kind = DataTypeKind::kLogic;
    } else if (Check(TokenKind::kLBracket)) {
      port.data_type.kind = DataTypeKind::kLogic;
      Consume();
      port.data_type.packed_dim_left = ParseExpr();
      Expect(TokenKind::kColon);
      port.data_type.packed_dim_right = ParseExpr();
      Expect(TokenKind::kRBracket);
    }
  }

  auto name_tok = ExpectIdentifier();
  port.name = name_tok.text;

  // A.2.1.2: unpacked dimensions (list_of_port_identifiers,
  // list_of_variable_identifiers, list_of_variable_port_identifiers)
  ParseUnpackedDims(port.unpacked_dims);

  if (Match(TokenKind::kEq)) {
    port.default_value = ParseExpr();
  }
  return port;
}

static bool HasNonAnsiPorts(const ModuleDecl& mod) {
  if (mod.ports.empty()) return false;
  return mod.ports[0].direction == Direction::kNone;
}

void Parser::ParseModuleBody(ModuleDecl& mod) {
  auto* prev_module = current_module_;
  current_module_ = &mod;
  bool non_ansi = HasNonAnsiPorts(mod);
  while (!Check(TokenKind::kKwEndmodule) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;  // null module item
    if (non_ansi && IsPortDirection(CurrentToken().kind)) {
      ParseNonAnsiPortDecls(mod);
      continue;
    }
    ParseModuleItem(mod.items);
  }
  current_module_ = prev_module;
}

void Parser::ParseNonAnsiPortDecls(ModuleDecl& mod) {
  Direction dir = Direction::kNone;
  auto tk = CurrentToken().kind;
  if (tk == TokenKind::kKwInput) dir = Direction::kInput;
  if (tk == TokenKind::kKwOutput) dir = Direction::kOutput;
  if (tk == TokenKind::kKwInout) dir = Direction::kInout;
  if (tk == TokenKind::kKwRef) dir = Direction::kRef;
  Consume();  // direction keyword

  auto dtype = ParseDataType();

  // Handle implicit type with packed dims: input [7:0] a;
  if (dtype.kind == DataTypeKind::kImplicit && Check(TokenKind::kLBracket)) {
    Consume();
    dtype.packed_dim_left = ParseExpr();
    Expect(TokenKind::kColon);
    dtype.packed_dim_right = ParseExpr();
    Expect(TokenKind::kRBracket);
  }

  // Parse comma-separated names with optional unpacked dims: input [7:0] a, b;
  // A.2.1.2: list_of_port_identifiers / list_of_variable_port_identifiers
  do {
    auto name = Expect(TokenKind::kIdentifier).text;
    std::vector<Expr*> dims;
    ParseUnpackedDims(dims);
    for (auto& port : mod.ports) {
      if (port.name != name) continue;
      port.direction = dir;
      port.data_type = dtype;
      port.unpacked_dims = std::move(dims);
      break;
    }
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
}

}  // namespace delta
