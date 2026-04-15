#include <format>
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
    std::vector<std::pair<std::string_view, Expr*>>& params,
    std::unordered_set<std::string_view>& type_param_names,
    std::unordered_set<std::string_view>& localparam_port_names,
    bool& is_localparam_group) {
  if (Match(TokenKind::kKwLocalparam)) {
    is_localparam_group = true;
  } else if (Match(TokenKind::kKwParameter)) {
    is_localparam_group = false;
  }
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
    type_param_names.insert(name.text);
    if (is_localparam_group) localparam_port_names.insert(name.text);
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
  if (is_localparam_group) localparam_port_names.insert(name.text);
}

void Parser::ParseParamsPortsAndSemicolon(ModuleDecl& decl) {
  // Optional package imports in module header (§26.4)
  while (Check(TokenKind::kKwImport)) {
    ParseImportDecl(decl.items);
  }
  if (Check(TokenKind::kHash)) {
    Consume();
    Expect(TokenKind::kLParen);
    decl.has_param_port_list = true;
    if (!Check(TokenKind::kRParen)) {
      bool is_lp_group = false;
      ParseParamPortDecl(decl.params, decl.type_param_names,
                         decl.localparam_port_names, is_lp_group);
      while (Match(TokenKind::kComma)) {
        ParseParamPortDecl(decl.params, decl.type_param_names,
                           decl.localparam_port_names, is_lp_group);
      }
    }
    Expect(TokenKind::kRParen);
  }
  if (Check(TokenKind::kLParen)) {
    ParsePortList(decl);
  }
  Expect(TokenKind::kSemicolon);
}

// §23.2.2.3: Apply default direction, port kind, and data type to a port.
// If prev is non-null, direction is inherited from the previous port when
// omitted.  Port kind and data type always follow first-port rules.
static void ResolvePortDefaults(PortDecl& port, const PortDecl* prev) {
  if (port.is_interface_port) return;
  if (port.data_type.kind == DataTypeKind::kNamed &&
      !port.data_type.modport_name.empty())
    return;

  if (port.is_explicit_named) {
    if (prev && port.direction == Direction::kNone)
      port.direction = prev->direction;
    return;
  }

  // F1 / S2: direction defaults to inout (first) or inherits (subsequent).
  if (port.direction == Direction::kNone)
    port.direction = prev ? prev->direction : Direction::kInout;

  // F3–F6: port kind (is_net) — must run before F2 to see kImplicit.
  if (!port.has_explicit_var && !port.data_type.is_net) {
    switch (port.direction) {
      case Direction::kInput:
      case Direction::kInout:
        port.data_type.is_net = true;
        break;
      case Direction::kOutput:
        if (port.data_type.kind == DataTypeKind::kImplicit)
          port.data_type.is_net = true;
        break;
      default:
        break;
    }
  }

  // F2: implicit data type defaults to logic.
  if (port.data_type.kind == DataTypeKind::kImplicit)
    port.data_type.kind = DataTypeKind::kLogic;
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
  // §A.1.3: Non-ANSI port list forms start with . or {.
  if (Check(TokenKind::kDot) || Check(TokenKind::kLBrace)) {
    ParseNonAnsiPortList(mod);
    return;
  }
  // Detect non-ANSI style: first token is an identifier (no direction/type).
  if (CheckIdentifier()) {
    if (known_types_.count(CurrentToken().text) != 0) {
      // Known type → ANSI (interface_port_header or typed port).
    } else {
      // Lookahead to distinguish non-ANSI port name from ANSI interface port.
      auto saved = lexer_.SavePos();
      Consume();
      bool is_non_ansi = Check(TokenKind::kRParen) ||
                          Check(TokenKind::kComma) ||
                          Check(TokenKind::kLBracket);
      lexer_.RestorePos(saved);
      if (is_non_ansi) {
        ParseNonAnsiPortList(mod);
        return;
      }
    }
  }
  mod.ports.push_back(ParsePortDecl());
  ResolvePortDefaults(mod.ports.back(), nullptr);
  while (Match(TokenKind::kComma)) {
    PortDecl prev = mod.ports.back();
    // §23.2.2.3 S1: detect all-omitted subsequent port (bare identifier
    // possibly followed by unpacked dims / default value).
    if (CheckIdentifier() && known_types_.count(CurrentToken().text) == 0) {
      auto saved = lexer_.SavePos();
      Consume();
      bool looks_bare = Check(TokenKind::kLBracket) || Check(TokenKind::kEq) ||
                        Check(TokenKind::kComma) || Check(TokenKind::kRParen);
      lexer_.RestorePos(saved);
      if (looks_bare) {
        PortDecl port;
        port.loc = CurrentLoc();
        port.name = ExpectIdentifier().text;
        ParseUnpackedDims(port.unpacked_dims);
        if (Match(TokenKind::kEq)) port.default_value = ParseExpr();
        if (!prev.is_explicit_named) {
          port.direction = prev.direction;
          port.data_type = prev.data_type;
        } else {
          // E2: after an explicit port, inherit only direction.
          ResolvePortDefaults(port, &prev);
        }
        mod.ports.push_back(port);
        continue;
      }
    }
    mod.ports.push_back(ParsePortDecl());
    ResolvePortDefaults(mod.ports.back(), &prev);
  }
  Expect(TokenKind::kRParen);
}

void Parser::ParseNonAnsiPortList(ModuleDecl& mod) {
  mod.is_non_ansi_ports = true;
  // §A.1.3 list_of_ports: port { , port }
  do {
    // §23.2.2.1: Empty port slots are allowed (e.g., module m(a, , b)).
    if (Check(TokenKind::kComma) || Check(TokenKind::kRParen)) {
      PortDecl port;
      port.loc = CurrentLoc();
      mod.ports.push_back(port);
      continue;
    }
    PortDecl port;
    port.loc = CurrentLoc();
    if (Match(TokenKind::kDot)) {
      // §A.1.3 port: . port_identifier ( [ port_expression ] )
      port.is_explicit_named = true;
      port.name = ExpectIdentifier().text;
      Expect(TokenKind::kLParen);
      if (!Check(TokenKind::kRParen)) {
        port.port_expr = ParseExpr();
      }
      Expect(TokenKind::kRParen);
    } else if (Check(TokenKind::kLBrace)) {
      // §A.1.3 port_expression: { port_reference { , port_reference } }
      port.port_expr = ParseExpr();
    } else {
      // §A.1.3 port_reference: port_identifier [ constant_select ]
      port.name = ExpectIdentifier().text;
      if (Check(TokenKind::kLBracket)) {
        auto* ref = arena_.Create<Expr>();
        ref->kind = ExprKind::kIdentifier;
        ref->text = port.name;
        Consume();
        auto* idx = ParseExpr();
        auto* sel = arena_.Create<Expr>();
        sel->kind = ExprKind::kSelect;
        sel->base = ref;
        sel->index = idx;
        if (Match(TokenKind::kColon)) {
          sel->index_end = ParseExpr();
        }
        Expect(TokenKind::kRBracket);
        port.port_expr = sel;
      }
    }
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

  // §A.1.3 ansi_port_declaration: [direction] . port_identifier ( [expression] )
  if (Check(TokenKind::kDot)) {
    port.is_explicit_named = true;
    Consume();
    port.name = ExpectIdentifier().text;
    Expect(TokenKind::kLParen);
    if (!Check(TokenKind::kRParen)) {
      port.port_expr = ParseExpr();
    }
    Expect(TokenKind::kRParen);
    return port;
  }

  // §A.1.3 interface_port_header: interface [ . modport_identifier ] port_name
  if (Check(TokenKind::kKwInterface)) {
    Consume();
    port.is_interface_port = true;
    if (Match(TokenKind::kDot)) {
      port.data_type.modport_name = ExpectIdentifier().text;
    }
    port.name = ExpectIdentifier().text;
    ParseUnpackedDims(port.unpacked_dims);
    if (Match(TokenKind::kEq)) {
      port.default_value = ParseExpr();
    }
    return port;
  }

  // §A.1.3 interface_port_header: ident . modport_ident port_name
  // Lookahead for unknown interface identifier followed by .modport pattern.
  if (dir == Direction::kNone && CheckIdentifier() &&
      known_types_.count(CurrentToken().text) == 0) {
    auto saved = lexer_.SavePos();
    auto id_tok = Consume();
    if (Check(TokenKind::kDot)) {
      Consume();
      if (CheckIdentifier()) {
        auto modport_tok = Consume();
        if (CheckIdentifier()) {
          port.data_type.kind = DataTypeKind::kNamed;
          port.data_type.type_name = id_tok.text;
          port.data_type.modport_name = modport_tok.text;
          port.name = ExpectIdentifier().text;
          ParseUnpackedDims(port.unpacked_dims);
          if (Match(TokenKind::kEq)) {
            port.default_value = ParseExpr();
          }
          return port;
        }
      }
    }
    lexer_.RestorePos(saved);
  }

  // A.2.1.2: variable_port_type ::= var_data_type
  // var_data_type ::= data_type | var data_type_or_implicit
  if (Match(TokenKind::kKwVar)) {
    port.has_explicit_var = true;
    port.data_type = ParseDataType();
    if (port.data_type.kind == DataTypeKind::kImplicit &&
        Check(TokenKind::kLBracket)) {
      ParsePackedDims(port.data_type);
    }
  } else if (Check(TokenKind::kKwStruct) || Check(TokenKind::kKwUnion)) {
    port.data_type = ParseStructOrUnionType();
    ParsePackedDims(port.data_type);
  } else {
    port.data_type = ParseDataType();
  }

  // §A.1.3 interface_port_header: known_type . modport_identifier
  if (port.data_type.kind == DataTypeKind::kNamed && Check(TokenKind::kDot)) {
    Consume();
    port.data_type.modport_name = ExpectIdentifier().text;
  }

  // Handle implicit type with bare packed dims: input [3:0] a (§6.10)
  if (port.data_type.kind == DataTypeKind::kImplicit &&
      !port.data_type.packed_dim_left && Check(TokenKind::kLBracket)) {
    Consume();
    port.data_type.packed_dim_left = ParseExpr();
    Expect(TokenKind::kColon);
    port.data_type.packed_dim_right = ParseExpr();
    Expect(TokenKind::kRBracket);
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
  auto& first = mod.ports[0];
  if (first.direction != Direction::kNone) return false;
  // ANSI ports with interface_port_header or named type have kNone direction.
  if (first.is_interface_port) return false;
  if (first.data_type.kind != DataTypeKind::kImplicit) return false;
  return true;
}

void Parser::ParseModuleBody(ModuleDecl& mod) {
  auto* prev_module = current_module_;
  current_module_ = &mod;
  bool non_ansi = HasNonAnsiPorts(mod);
  // [ timeunits_declaration ] — header area per module_declaration grammar
  if (Check(TokenKind::kKwTimeunit) || Check(TokenKind::kKwTimeprecision)) {
    bool first_is_unit = Check(TokenKind::kKwTimeunit);
    ParseTimeunitDecl(&mod);
    if (first_is_unit && !mod.has_timeprecision &&
        Check(TokenKind::kKwTimeprecision)) {
      ParseTimeunitDecl(&mod);
    } else if (!first_is_unit && !mod.has_timeunit &&
               Check(TokenKind::kKwTimeunit)) {
      ParseTimeunitDecl(&mod);
    }
  }
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
    auto loc = CurrentLoc();
    auto name = Expect(TokenKind::kIdentifier).text;
    std::vector<Expr*> dims;
    ParseUnpackedDims(dims);
    bool found = false;
    for (auto& port : mod.ports) {
      if (port.name != name) continue;
      // §23.2.2.1 R13: A port shall not be declared in more than one
      // port declaration.
      if (!found && port.direction != Direction::kNone) {
        diag_.Error(loc,
                    std::format("duplicate port declaration for '{}'", name));
      }
      found = true;
      port.direction = dir;
      port.data_type = dtype;
      port.unpacked_dims = dims;
    }
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
}

}  // namespace delta
