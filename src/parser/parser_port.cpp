#include <cctype>
#include <format>
#include <optional>
#include <string_view>

#include "common/types.h"
#include "parser/parser.h"

namespace delta {

static bool IsValidCIdentifier(std::string_view text) {
  if (text.empty()) return false;
  auto first = static_cast<unsigned char>(text.front());
  if (!std::isalpha(first) && first != '_') return false;
  for (char ch : text.substr(1)) {
    auto c = static_cast<unsigned char>(ch);
    if (!std::isalnum(c) && c != '_') return false;
  }
  return true;
}

// §35.5.4: dpi_spec_string ::= "DPI-C" | "DPI". The lexer keeps the raw
// quoted text in the token; this returns the inner characters so the rest
// of the parser can compare against the two literal values from Syntax 35-1.
static std::string_view StripStringLiteralQuotes(std::string_view text) {
  if (text.size() < 2) return text;
  if (text.front() != '"' || text.back() != '"') return text;
  return text.substr(1, text.size() - 2);
}

// CPD-dedup: the dpi_spec_string parse/validation and the optional
// "= c_identifier" tail are identical between DPI import and export.
struct ParserPortHelpers {
  static void ParseDpiSpecString(Parser& p, ModuleItem* item) {
    auto spec_tok = p.Consume();
    item->dpi_spec_string = StripStringLiteralQuotes(spec_tok.text);
    if (item->dpi_spec_string == "DPI") {
      // §35.5.4: "DPI" is deprecated; the warning text must point at the
      // canonical replacement and warn about possible C-code changes.
      p.diag_.Warning(
          spec_tok.loc,
          "\"DPI\" is deprecated and should be replaced with \"DPI-C\"; "
          "use of the \"DPI-C\" string may require changes to the DPI "
          "application's C code");
    } else if (item->dpi_spec_string != "DPI-C") {
      p.diag_.Error(spec_tok.loc,
                    "DPI specification string must be \"DPI-C\" or \"DPI\"");
    }
  }

  static void TryParseDpiCName(Parser& p, ModuleItem* item) {
    if (p.Check(TokenKind::kIdentifier)) {
      auto saved = p.lexer_.SavePos();
      auto tok = p.Consume();
      if (p.Match(TokenKind::kEq)) {
        if (!IsValidCIdentifier(tok.text)) {
          p.diag_.Error(tok.loc,
                        "DPI c_identifier must match [a-zA-Z_][a-zA-Z0-9_]*");
        }
        item->dpi_c_name = tok.text;
      } else {
        p.lexer_.RestorePos(saved);
      }
    }
  }
};

// §35.5.6: a rich but closed subset of SystemVerilog data types is permitted
// for the formal arguments of DPI import/export subroutines. The clause states
// these are the *only* permitted types: the C-compatible scalar types, the
// scalar 2-/4-state bit types, packed arrays/structs/unions of bit and logic,
// enumerations (interpreted as their base type), and user-defined types
// (typedef/named) built from the above. Anything outside that set -- notably
// event types, virtual interfaces, and net types -- is not a permitted formal
// argument type. Named/typedef forms are accepted here because their underlying
// type is only known after elaboration, and typedef is itself a permitted
// construct per the clause.
static bool IsPermittedDpiFormalType(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kImplicit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kBit:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
    case DataTypeKind::kTime:
    case DataTypeKind::kString:
    case DataTypeKind::kVoid:
    case DataTypeKind::kChandle:
    case DataTypeKind::kNamed:
    case DataTypeKind::kEnum:
    case DataTypeKind::kStruct:
    case DataTypeKind::kUnion:
      return true;
    default:
      return false;
  }
}

// §35.5.5: the result type of an imported function is restricted to "small
// values" -- a tighter set than the §35.5.6 formal-argument types. The
// permitted results are void, the C-compatible scalar integer and real types,
// chandle, string, and *scalar* (single-bit, unpacked) bit/logic. Packed
// bit/logic vectors, the wide 4-state vector types (integer, time), and
// aggregates (struct/union/enum) are not small values and are rejected here.
// Named/typedef results are accepted and deferred to elaboration, since the
// underlying type is not resolved during parsing. The implicit (omitted) kind
// is handled separately, since §35.5.5 also requires the result type to be
// stated explicitly.
static bool IsPermittedDpiResultType(const DataType& type) {
  switch (type.kind) {
    case DataTypeKind::kVoid:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
    case DataTypeKind::kChandle:
    case DataTypeKind::kString:
    case DataTypeKind::kNamed:
      return true;
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      // Only the scalar form qualifies; any packed dimension makes it a vector.
      return type.packed_dim_left == nullptr && type.extra_packed_dims.empty();
    default:
      return false;
  }
}

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

  if (CurrentToken().kind == TokenKind::kSystemIdentifier &&
      CurrentToken().text == "$unit") {
    diag_.Error(CurrentLoc(),
                "the compilation-unit scope cannot be used with an "
                "import declaration");
    Consume();
    if (Check(TokenKind::kColonColon)) Consume();
    if (Check(TokenKind::kStar)) {
      Consume();
      item->import_item.is_wildcard = true;
    } else if (Check(TokenKind::kIdentifier)) {
      item->import_item.item_name = Consume().text;
    }
    return item;
  }
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

  if (Check(TokenKind::kStringLiteral)) {
    items.push_back(ParseDpiExport(loc));
    return;
  }
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kExportDecl;
  item->loc = loc;
  if (Match(TokenKind::kStar)) {
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
  ParserPortHelpers::ParseDpiSpecString(*this, item);

  if (Match(TokenKind::kKwPure)) {
    item->dpi_is_pure = true;
  }
  if (Match(TokenKind::kKwContext)) {
    item->dpi_is_context = true;
  }

  ParserPortHelpers::TryParseDpiCName(*this, item);

  if (Match(TokenKind::kKwTask)) {
    item->dpi_is_task = true;
  } else {
    Expect(TokenKind::kKwFunction);
  }

  // §35.5.1.3: the pure property is reserved for imported functions; an
  // imported task can never be declared pure.
  if (item->dpi_is_task && item->dpi_is_pure) {
    diag_.Error(item->loc, "an imported task cannot be declared pure");
  }

  if (!item->dpi_is_task) {
    item->return_type = ParseDataType();
    // §35.5.5: an imported function declaration shall explicitly specify a data
    // type or void for its result. Unlike a native function declaration, an
    // omitted (implicit) return type is not allowed.
    if (item->return_type.kind == DataTypeKind::kImplicit) {
      diag_.Error(item->loc,
                  "an imported function must explicitly specify a data type or "
                  "void for its result");
    } else if (!IsPermittedDpiResultType(item->return_type)) {
      // §35.5.5: function results are restricted to small values; the type is
      // outside the permitted set.
      diag_.Error(item->loc,
                  "result type is not permitted for a DPI imported function; "
                  "function results are restricted to small values");
    }
  }
  item->name = Expect(TokenKind::kIdentifier).text;

  if (Check(TokenKind::kLParen)) {
    item->func_args = ParseFunctionArgs(false);
  }
  // §35.5.4: ref qualifier is forbidden in import declarations.
  for (const auto& arg : item->func_args) {
    if (arg.direction == Direction::kRef) {
      diag_.Error(item->loc,
                  "ref qualifier cannot be used in a DPI import declaration");
      break;
    }
  }
  // §35.5.6: the listed types are the only permitted types for formal
  // arguments of imported subroutines. Reject any formal argument whose type
  // falls outside that closed set.
  for (const auto& arg : item->func_args) {
    if (!IsPermittedDpiFormalType(arg.data_type.kind)) {
      diag_.Error(item->loc,
                  std::format("type of formal argument '{}' is not permitted "
                              "for a DPI imported subroutine",
                              arg.name));
    } else if (arg.data_type.kind == DataTypeKind::kUnion &&
               !arg.data_type.is_packed) {
      // §35.5.6: among the type-constructing forms in the permitted set, a
      // union is allowed in its packed form only. An unpacked union is
      // therefore not a permitted formal-argument type.
      diag_.Error(item->loc,
                  std::format("unpacked union formal argument '{}' is not "
                              "permitted for a DPI imported subroutine; only "
                              "the packed form of a union is allowed",
                              arg.name));
    }
  }
  Expect(TokenKind::kSemicolon);
  return item;
}

ModuleItem* Parser::ParseDpiExport(SourceLoc loc) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kDpiExport;
  item->loc = loc;
  ParserPortHelpers::ParseDpiSpecString(*this, item);

  ParserPortHelpers::TryParseDpiCName(*this, item);

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
    bool& is_localparam_group, std::vector<DataType>* param_types) {
  if (Match(TokenKind::kKwLocalparam)) {
    is_localparam_group = true;
  } else if (Match(TokenKind::kKwParameter)) {
    is_localparam_group = false;
  }

  if (Match(TokenKind::kKwType)) {
    // A type_parameter_declaration may carry an optional forward_type keyword
    // (enum, struct, union, class, or interface class) before the identifier
    // to restrict the kinds of type the parameter accepts.
    if (Match(TokenKind::kKwInterface)) {
      Expect(TokenKind::kKwClass);
    } else if (Check(TokenKind::kKwEnum) || Check(TokenKind::kKwStruct) ||
               Check(TokenKind::kKwUnion) || Check(TokenKind::kKwClass)) {
      Consume();
    }
    auto name = Expect(TokenKind::kIdentifier);
    bool has_default = false;
    if (Match(TokenKind::kEq)) {
      has_default = true;
      if (Check(TokenKind::kKwType)) {
        ParseExpr();
      } else {
        ParseDataType();
      }
    }

    if (is_localparam_group && !has_default) {
      diag_.Error(name.loc,
                  std::format("localparam type '{}' in parameter port list "
                              "must have a default type",
                              name.text));
    }
    params.push_back({name.text, nullptr});
    if (param_types) param_types->push_back(DataType{});
    type_param_names.insert(name.text);
    if (is_localparam_group) localparam_port_names.insert(name.text);
    known_types_.insert(name.text);
    return;
  }
  DataType dtype = ParseDataType();
  auto name = Expect(TokenKind::kIdentifier);
  Expr* default_val = nullptr;
  if (Match(TokenKind::kEq)) {
    default_val = ParseExpr();
  }

  if (is_localparam_group && default_val == nullptr) {
    diag_.Error(name.loc,
                std::format("localparam '{}' in parameter port list must "
                            "have a default value",
                            name.text));
  }
  params.push_back({name.text, default_val});
  if (param_types) param_types->push_back(dtype);
  if (is_localparam_group) localparam_port_names.insert(name.text);
}

void Parser::ParseParamsPortsAndSemicolon(ModuleDecl& decl) {
  SourceLoc import_loc;
  bool has_header_import = false;
  while (Check(TokenKind::kKwImport)) {
    if (!has_header_import) import_loc = CurrentLoc();
    has_header_import = true;
    size_t before = decl.items.size();
    ParseImportDecl(decl.items);
    for (size_t i = before; i < decl.items.size(); ++i) {
      decl.items[i]->import_item.is_header = true;
    }
  }
  if (has_header_import && !Check(TokenKind::kHash) &&
      !Check(TokenKind::kLParen)) {
    diag_.Error(import_loc,
                "package_import_declaration in ansi header must be followed "
                "by parameter_port_list or list_of_port_declarations");
  }
  if (Check(TokenKind::kHash)) {
    Consume();
    Expect(TokenKind::kLParen);
    decl.has_param_port_list = true;
    if (!Check(TokenKind::kRParen)) {
      bool is_lp_group = false;
      ParseParamPortDecl(decl.params, decl.type_param_names,
                         decl.localparam_port_names, is_lp_group,
                         &decl.param_types);
      while (Match(TokenKind::kComma)) {
        ParseParamPortDecl(decl.params, decl.type_param_names,
                           decl.localparam_port_names, is_lp_group,
                           &decl.param_types);
      }
    }
    Expect(TokenKind::kRParen);
  }
  if (Check(TokenKind::kLParen)) {
    ParsePortList(decl);
  }
  Expect(TokenKind::kSemicolon);
}

static void ResolvePortDefaults(PortDecl& port, const PortDecl* prev,
                                bool is_checker) {
  if (port.is_interface_port) return;
  if (port.data_type.kind == DataTypeKind::kNamed &&
      !port.data_type.modport_name.empty())
    return;

  if (port.is_explicit_named) {
    if (prev && port.direction == Direction::kNone)
      port.direction = prev->direction;
    return;
  }

  // §17.2: when a checker formal argument omits its direction, the direction
  // of the previous formal is inferred; the first formal defaults to input.
  // Module-style ports instead default to inout when no prior direction exists.
  if (port.direction == Direction::kNone)
    port.direction = prev
                         ? prev->direction
                         : (is_checker ? Direction::kInput : Direction::kInout);

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

  if (port.data_type.kind == DataTypeKind::kImplicit)
    port.data_type.kind = DataTypeKind::kLogic;
}

void Parser::ParsePortList(ModuleDecl& mod) {
  Expect(TokenKind::kLParen);
  if (Check(TokenKind::kRParen)) {
    Consume();
    return;
  }

  if (Check(TokenKind::kDotStar)) {
    Consume();
    mod.has_wildcard_ports = true;
    Expect(TokenKind::kRParen);
    return;
  }

  if (Check(TokenKind::kDot) || Check(TokenKind::kLBrace)) {
    ParseNonAnsiPortList(mod);
    return;
  }

  if (CheckIdentifier()) {
    if (known_types_.count(CurrentToken().text) != 0) {
    } else {
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
  const bool kIsChecker = mod.decl_kind == ModuleDeclKind::kChecker;
  mod.ports.push_back(ParsePortDecl());
  ResolvePortDefaults(mod.ports.back(), nullptr, kIsChecker);
  while (Match(TokenKind::kComma)) {
    PortDecl prev = mod.ports.back();

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
          ResolvePortDefaults(port, &prev, kIsChecker);
        }
        mod.ports.push_back(port);
        continue;
      }
    }
    mod.ports.push_back(ParsePortDecl());
    ResolvePortDefaults(mod.ports.back(), &prev, kIsChecker);
  }
  Expect(TokenKind::kRParen);
}

void Parser::ParseNonAnsiPortList(ModuleDecl& mod) {
  mod.is_non_ansi_ports = true;

  do {
    if (Check(TokenKind::kComma) || Check(TokenKind::kRParen)) {
      PortDecl port;
      port.loc = CurrentLoc();
      mod.ports.push_back(port);
      continue;
    }
    PortDecl port;
    port.loc = CurrentLoc();
    if (Match(TokenKind::kDot)) {
      port.is_explicit_named = true;
      port.name = ExpectIdentifier().text;
      Expect(TokenKind::kLParen);
      if (!Check(TokenKind::kRParen)) {
        port.port_expr = ParseExpr();
      }
      Expect(TokenKind::kRParen);
    } else if (Check(TokenKind::kLBrace)) {
      port.port_expr = ParseExpr();
    } else {
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

  // §A.1.3: each ansi_port_declaration in a list_of_port_declarations may be
  // preceded by attribute_instances. They carry no ANSI port semantics here,
  // so consume and discard them before the port itself.
  ParseAttributes();

  port.loc = CurrentLoc();

  Direction dir = TokenToDirection(CurrentToken().kind);
  if (dir != Direction::kNone) {
    port.direction = dir;
    Consume();
  }

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
  } else if (Match(TokenKind::kKwInterconnect)) {
    port.data_type.kind = DataTypeKind::kWire;
    port.data_type.is_net = true;
    port.data_type.is_interconnect = true;
    if (Match(TokenKind::kKwSigned)) {
      port.data_type.is_signed = true;
    } else {
      Match(TokenKind::kKwUnsigned);
    }
    ParsePackedDims(port.data_type);
  } else {
    port.data_type = ParseDataType();
  }

  if (port.data_type.kind == DataTypeKind::kNamed && Check(TokenKind::kDot)) {
    Consume();
    port.data_type.modport_name = ExpectIdentifier().text;
  }

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

  if (first.is_interface_port) return false;
  if (first.data_type.kind != DataTypeKind::kImplicit) return false;
  return true;
}

void Parser::ParseModuleBody(ModuleDecl& mod) {
  auto* prev_module = current_module_;
  current_module_ = &mod;
  bool non_ansi = HasNonAnsiPorts(mod);

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
    if (Match(TokenKind::kSemicolon)) continue;
    if (non_ansi && IsPortDirection(CurrentToken().kind)) {
      ParseNonAnsiPortDecls(mod);
      continue;
    }
    // §A.1.3: a non-ANSI body port_declaration may carry leading
    // attribute_instances. Peek past them; if a port direction follows, this is
    // a port declaration rather than a generic module item.
    if (non_ansi && Check(TokenKind::kAttrStart)) {
      auto saved = lexer_.SavePos();
      ParseAttributes();
      if (IsPortDirection(CurrentToken().kind)) {
        ParseNonAnsiPortDecls(mod);
        continue;
      }
      lexer_.RestorePos(saved);
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
  Consume();

  // §23.2.2.2 / §25.3.3: a generic interface reference uses the `interface`
  // keyword as a placeholder port type. Such a port may only be declared with
  // the ANSI list_of_port_declarations style; encountering it inside a non-ANSI
  // body port declaration means it was written with the non-ANSI list_of_ports
  // style, which is illegal.
  if (Check(TokenKind::kKwInterface)) {
    diag_.Error(CurrentLoc(),
                "generic interface port must be declared with ANSI-style port "
                "declarations, not the non-ANSI port style");
    while (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwEndmodule) &&
           !AtEnd())
      Consume();
    Match(TokenKind::kSemicolon);
    return;
  }

  auto dtype = ParseDataType();

  if (dtype.kind == DataTypeKind::kImplicit && Check(TokenKind::kLBracket)) {
    Consume();
    dtype.packed_dim_left = ParseExpr();
    Expect(TokenKind::kColon);
    dtype.packed_dim_right = ParseExpr();
    Expect(TokenKind::kRBracket);
  }

  do {
    auto loc = CurrentLoc();
    auto name = Expect(TokenKind::kIdentifier).text;
    std::vector<Expr*> dims;
    ParseUnpackedDims(dims);
    bool found = false;
    for (auto& port : mod.ports) {
      if (port.name != name) continue;

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
